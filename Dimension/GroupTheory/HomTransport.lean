module

public import Dimension.GroupTheory.BassSerreHoms

/-! # Transport of rational homomorphisms and cyclic coset orbits -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace WeightTwoCusps

def rationalHom_precomp {G K : Type*} [Group G] [Group K] (f : G →* K) :
    (Additive K →+ ℚ) →ₗ[ℚ] (Additive G →+ ℚ) where
  toFun φ := φ.comp f.toAdditive
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rationalHom_precomp_bijective {G K : Type*} [Group G] [Group K] (f : G →* K)
    (hf : Function.Surjective f) (hker : ∀ g : G, f g = 1 → IsOfFinOrder g) :
    Function.Bijective (rationalHom_precomp f) := by
  constructor
  · intro φ ψ h
    apply AddMonoidHom.ext
    intro k
    obtain ⟨g, hg⟩ := hf (Additive.toMul k)
    have h' := DFunLike.congr_fun h (Additive.ofMul g)
    change φ (Additive.ofMul (f g)) = ψ (Additive.ofMul (f g)) at h'
    rw [hg] at h'
    simpa only [ofMul_toMul] using h'
  · intro φ
    have hsame (g h : G) (hgh : f g = f h) :
        φ (Additive.ofMul g) = φ (Additive.ofMul h) := by
      have hz := rationalHom_eq_zero_of_isOfFinOrder φ (g * h⁻¹)
        (hker _ (by rw [map_mul, map_inv, hgh, mul_inv_cancel]))
      simp only [ofMul_mul, ofMul_inv, map_add, map_neg] at hz
      linarith
    choose s hs using hf
    let ψ : Additive K →+ ℚ :=
      { toFun := fun k => φ (Additive.ofMul (s (Additive.toMul k)))
        map_zero' := by
          exact (hsame (s 1) 1 (by rw [hs, map_one])).trans (map_zero φ)
        map_add' := by
          intro k l
          change φ (Additive.ofMul (s (Additive.toMul k * Additive.toMul l))) = _
          rw [hsame _ (s (Additive.toMul k) * s (Additive.toMul l))
            (by rw [hs, map_mul, hs, hs]), ofMul_mul, map_add] }
    refine ⟨ψ, AddMonoidHom.ext fun g => ?_⟩
    exact hsame _ (Additive.toMul g) (hs _)

theorem finrank_rationalHom_of_surjective {G K : Type*} [Group G] [Group K] (f : G →* K)
    (hf : Function.Surjective f) (hker : ∀ g : G, f g = 1 → IsOfFinOrder g) :
    Module.finrank ℚ (Additive K →+ ℚ) = Module.finrank ℚ (Additive G →+ ℚ) :=
  (LinearEquiv.ofBijective (rationalHom_precomp f) (rationalHom_precomp_bijective f hf hker)).finrank_eq

def comapCosetMap {G K : Type*} [Group G] [Group K] (f : G →* K) (H : Subgroup K) :
    (G ⧸ H.comap f) → (K ⧸ H) :=
  Quotient.map' f (by
    intro x y hxy
    rw [QuotientGroup.leftRel_apply] at hxy ⊢
    simpa only [Subgroup.mem_comap, map_mul, map_inv] using hxy)

theorem comapCosetMap_bijective {G K : Type*} [Group G] [Group K] (f : G →* K)
    (hf : Function.Surjective f) (H : Subgroup K) : Function.Bijective (comapCosetMap f H) := by
  constructor
  · intro q r hqr
    induction q using QuotientGroup.induction_on with
    | H g =>
      induction r using QuotientGroup.induction_on with
      | H k =>
        apply QuotientGroup.eq.mpr
        have h := QuotientGroup.eq.mp hqr
        simpa only [Subgroup.mem_comap, map_mul, map_inv] using h
  · intro q
    induction q using QuotientGroup.induction_on with
    | H k =>
      obtain ⟨g, rfl⟩ := hf k
      exact ⟨g, rfl⟩

theorem comapCosetMap_smul {G K : Type*} [Group G] [Group K] (f : G →* K)
    (H : Subgroup K) (g : G) (q : G ⧸ H.comap f) :
    comapCosetMap f H (g • q) = f g • comapCosetMap f H q := by
  induction q using QuotientGroup.induction_on with
  | H k => change (f (g * k) : K ⧸ H) = (f g * f k : K); rw [map_mul]

def comapCyclicOrbitMap {G K : Type*} [Group G] [Group K] (f : G →* K)
    (H : Subgroup K) (u : G) :
    MulAction.orbitRel.Quotient (Subgroup.zpowers u) (G ⧸ H.comap f) →
      MulAction.orbitRel.Quotient (Subgroup.zpowers (f u)) (K ⧸ H) :=
  Quotient.map' (comapCosetMap f H) (by
    intro q r hqr
    obtain ⟨v, hv⟩ := MulAction.orbitRel_apply.mp hqr
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp v.property
    apply MulAction.orbitRel_apply.mpr
    refine ⟨⟨(f u) ^ j, Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) j⟩, ?_⟩
    change (f u) ^ j • comapCosetMap f H r = comapCosetMap f H q
    rw [← map_zpow, ← comapCosetMap_smul]
    change (v.val : G) • r = q at hv
    rw [← hj] at hv
    exact congrArg (comapCosetMap f H) hv)

theorem comapCyclicOrbitMap_bijective {G K : Type*} [Group G] [Group K] (f : G →* K)
    (hf : Function.Surjective f) (H : Subgroup K) (u : G) :
    Function.Bijective (comapCyclicOrbitMap f H u) := by
  have hcoset := comapCosetMap_bijective f hf H
  constructor
  · intro q r hqr
    induction q using Quotient.inductionOn with
    | h q =>
      induction r using Quotient.inductionOn with
      | h r =>
        obtain ⟨v, hv⟩ := MulAction.orbitRel_apply.mp (Quotient.exact hqr)
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp v.property
        apply Quotient.sound
        apply MulAction.orbitRel_apply.mpr
        refine ⟨⟨u ^ j, Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) j⟩, ?_⟩
        change (u ^ j : G) • r = q
        apply hcoset.1
        rw [comapCosetMap_smul, map_zpow]
        change (f u) ^ j • comapCosetMap f H r = comapCosetMap f H q
        change (v.val : K) • comapCosetMap f H r = comapCosetMap f H q at hv
        simpa only [hj] using hv
  · intro q
    induction q using Quotient.inductionOn with
    | h q =>
      obtain ⟨r, rfl⟩ := hcoset.2 q
      exact ⟨⟦r⟧, rfl⟩

theorem card_comap_cyclic_orbits {G K : Type*} [Group G] [Group K] (f : G →* K)
    (hf : Function.Surjective f) (H : Subgroup K) (u : G) :
    Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers u) (G ⧸ H.comap f)) =
      Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers (f u)) (K ⧸ H)) :=
  Nat.card_eq_of_bijective _ (comapCyclicOrbitMap_bijective f hf H u)

end WeightTwoCusps
