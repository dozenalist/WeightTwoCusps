module

public import Dimension.FLT.P2M.Sol.S_Monoid_CoprodI_nonempty_freeGroupBasis_fin_kuroshRank
public import Dimension.GroupTheory.TreePotentials

/-! # Rational homomorphisms on a tree with finite vertex stabilizers

This extends the rational part of the attributed FLT Bass--Serre construction
without assuming a free vertex action. The tree, connected transversal, and
translation representatives are those of the retained upstream module; see
`Dimension/FLT/ATTRIBUTION_UPSTREAM.md`.
-/

@[expose] public section

noncomputable section

open P2MW.S_Monoid_CoprodI_nonempty_freeGroupBasis_fin_kuroshRank.GroupTheory
open Monoid
open scoped P2MW.S_Monoid_CoprodI_nonempty_freeGroupBasis_fin_kuroshRank.GroupTheory.BassSerre

namespace WeightTwoCusps

/-- Rational additive homomorphisms kill every finite-order group element. -/
theorem rationalHom_eq_zero_of_isOfFinOrder {H : Type*} [Group H]
    (φ : Additive H →+ ℚ) (h : H) (hh : IsOfFinOrder h) :
    φ (Additive.ofMul h) = 0 := by
  obtain ⟨n, hn, hpow⟩ := hh.exists_pow_eq_one
  have hzero : n • φ (Additive.ofMul h) = 0 := by
    rw [← map_nsmul, ← ofMul_pow, hpow, ofMul_one, map_zero]
  exact (mul_eq_zero.mp (by simpa only [nsmul_eq_mul] using hzero)).resolve_left
    (Nat.cast_ne_zero.mpr hn.ne')

namespace BassSerreHoms

open BassSerre GraphTransversal

variable {G : Fin 2 → Type*} [∀ i, Group (G i)] [∀ i, Finite (G i)]
  {H : Subgroup (CoprodI G)} {D : Set (Vertex G)}

/-- Vertex stabilizers in a free product of finite groups consist of torsion. -/
theorem stabilizer_isOfFinOrder (η : H) (v : Vertex G) (hfix : η • v = v) :
    IsOfFinOrder η := by
  rcases v with ⟨i, q⟩
  induction q using QuotientGroup.induction_on with
  | H g =>
    have hm : g⁻¹ * (η : CoprodI G) * g ∈ (CoprodI.of (M := G) (i := i)).range :=
      smul_eq_self_iff.mp hfix
    let : Finite ((CoprodI.of (M := G) (i := i)).range) :=
      Finite.of_equiv (G i) (MonoidHom.ofInjective (CoprodI.of_injective i)).toEquiv
    have hc := Kurosh.isOfFinOrder_of_mem_finite hm
    have hh := Kurosh.isOfFinOrder_conj g⁻¹ hc
    have heq : g⁻¹⁻¹ * (g⁻¹ * (η : CoprodI G) * g) * g⁻¹ = (η : CoprodI G) := by group
    rw [heq] at hh
    exact Submonoid.isOfFinOrder_coe.mp hh

theorem hom_eq_zero_of_fixes (φ : Additive H →+ ℚ) (η : H) (v : Vertex G)
    (hfix : η • v = v) : φ (Additive.ofMul η) = 0 :=
  rationalHom_eq_zero_of_isOfFinOrder φ η (stabilizer_isOfFinOrder η v hfix)

variable (hD : IsConnectedTransversal (graph G) H D)

/-- A translation representative at a transversal vertex may be nontrivial,
but its value under every rational homomorphism is zero. -/
theorem hom_transl_eq_zero (φ : Additive H →+ ℚ) {v : Vertex G} (hv : v ∈ D) :
    φ (Additive.ofMul (transl hD v)) = 0 := by
  apply hom_eq_zero_of_fixes φ _ v
  have h := transl_smul_orbitRepr hD v
  rwa [orbitRepr_eq_self hD hv] at h

/-- Translation representatives are equivariant after applying a rational
homomorphism, even when vertex stabilizers are nontrivial. -/
theorem hom_transl_smul (φ : Additive H →+ ℚ) (η : H) (v : Vertex G) :
    φ (Additive.ofMul (transl hD (η • v))) =
      φ (Additive.ofMul η) + φ (Additive.ofMul (transl hD v)) := by
  let δ : H := (transl hD (η • v))⁻¹ * η * transl hD v
  have hfix : δ • orbitRepr hD v = orbitRepr hD v := by
    have ht := transl_smul_orbitRepr hD (η • v)
    rw [orbitRepr_smul hD η v] at ht
    simp only [δ, mul_smul, transl_smul_orbitRepr]
    exact inv_smul_eq_iff.mpr ht.symm
  have hz := hom_eq_zero_of_fixes φ δ _ hfix
  simp only [δ, ofMul_mul, ofMul_inv, map_add, map_neg] at hz
  linarith

/-- The edge-generator value is constant on subgroup edge orbits. -/
theorem hom_edgeGen_smul (φ : Additive H →+ ℚ) (η : H) (g : CoprodI G) :
    φ (Additive.ofMul (edgeGen hD ((η : CoprodI G) * g))) =
      φ (Additive.ofMul (edgeGen hD g)) := by
  simp only [edgeGen, ofMul_mul, ofMul_inv, map_add, map_neg]
  change -φ (Additive.ofMul (transl hD (η • Vertex.mk 0 g))) +
    φ (Additive.ofMul (transl hD (η • Vertex.mk 1 g))) = _
  rw [hom_transl_smul, hom_transl_smul]
  ring

/-- Edges lying inside the connected transversal contribute no homomorphism value. -/
theorem hom_edgeGen_eq_zero (φ : Additive H →+ ℚ) (g : CoprodI G)
    (h₀ : Vertex.mk 0 g ∈ D) (h₁ : Vertex.mk 1 g ∈ D) :
    φ (Additive.ofMul (edgeGen hD g)) = 0 := by
  simp only [edgeGen, ofMul_mul, ofMul_inv, map_add, map_neg,
    hom_transl_eq_zero hD φ h₀, hom_transl_eq_zero hD φ h₁, neg_zero, add_zero]

/-- Edge-generator values determine every rational homomorphism. This replaces
the free-action generation argument by killing finite vertex stabilizers. -/
theorem hom_eq_zero_of_edgeGen (φ : Additive H →+ ℚ)
    (hφ : ∀ g : CoprodI G, φ (Additive.ofMul (edgeGen hD g)) = 0) : φ = 0 := by
  let K : Subgroup H :=
    { carrier := {η | φ (Additive.ofMul η) = 0}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq, ofMul_mul, map_add] at *
        rw [ha, hb, add_zero]
      inv_mem' := by
        intro a ha
        simpa only [Set.mem_ofPred_eq, ofMul_inv, map_neg, neg_eq_zero] using ha }
  have hker : Subgroup.closure (Set.range (edgeGen hD)) ≤ K := by
    rw [Subgroup.closure_le]
    rintro _ ⟨g, rfl⟩
    exact hφ g
  obtain ⟨d, hd, -⟩ := hD.exists_mem_orbit (Vertex.mk 0 1)
  apply AddMonoidHom.ext
  intro x
  let η : H := Additive.toMul x
  obtain ⟨p⟩ := BassSerre.connected.preconnected d (η • d)
  have hz := hker (inv_mul_transl_mem_closure_of_walk hD p)
  change φ (Additive.ofMul ((transl hD d)⁻¹ * transl hD (η • d))) = 0 at hz
  rw [ofMul_mul, ofMul_inv, map_add, map_neg, hom_transl_smul,
    hom_transl_eq_zero hD φ hd, neg_zero, add_zero, zero_add] at hz
  exact hz

/-- Evaluation on subgroup edge orbits. Inversion identifies left edge orbits
with the standard right coset quotient. -/
def edgeEvaluation : (Additive H →+ ℚ) →ₗ[ℚ] ((CoprodI G ⧸ H) → ℚ) where
  toFun φ := Quotient.lift (fun g => φ (Additive.ofMul (edgeGen hD g⁻¹))) (by
    intro g k hgk
    have hm : g⁻¹ * k ∈ H := QuotientGroup.leftRel_apply.mp hgk
    let η : H := ⟨g⁻¹ * k, hm⟩
    have heq : k⁻¹ = ((η⁻¹ : H) : CoprodI G) * g⁻¹ := by
      change k⁻¹ = (g⁻¹ * k)⁻¹ * g⁻¹
      group
    rw [heq, hom_edgeGen_smul])
  map_add' φ ψ := by
    funext q
    induction q using QuotientGroup.induction_on with
    | H g => rfl
  map_smul' r φ := by
    funext q
    induction q using QuotientGroup.induction_on with
    | H g => rfl

theorem edgeEvaluation_injective : Function.Injective (edgeEvaluation hD) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro φ hφ
  apply hom_eq_zero_of_edgeGen hD φ
  intro g
  have h := congrFun hφ ((g⁻¹ : CoprodI G) : CoprodI G ⧸ H)
  simpa only [edgeEvaluation, LinearMap.coe_mk, AddHom.coe_mk, Quotient.lift_mk,
    inv_inv, Pi.zero_apply] using h

end BassSerreHoms

end WeightTwoCusps
