module

public import WeightTwoCusps.EtaQuotient.Transformation.Generation
public import WeightTwoCusps.Eta.Congruence
public import Mathlib.Data.ZMod.Units

/-!
# Descent from a restricted arithmetic multiplier formula

The subgroup with lower-left entry divisible by `MN` and upper-right entry
divisible by `M` maps onto the diagonal quotient `Γ₀(N)/Γ₁(N)`. Consequently,
invariance under this restricted subgroup and under `Γ₁(N)` suffices for
invariance under `Γ₀(N)`.

The intended application takes `M = 24`. This lets the sufficiency argument
use the restricted eta-multiplier formula without first constructing the
quadratic character on all of `Γ₀(N)`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped MatrixGroups ModularForm
open UpperHalfPlane

namespace WeightTwoCusps.EtaQuotient

private theorem diagonal_product_eq_one {N : ℕ} (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    (γ 0 0 : ZMod N) * γ 1 1 = 1 := by
  have h := congrArg (Int.cast : ℤ → ZMod N) γ.det_coe
  simpa only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one,
    CongruenceSubgroup.Gamma0_mem.mp hγ, mul_zero, sub_zero] using h

/-- Lift a bottom-right entry modulo `N` while imposing arbitrary common
off-diagonal divisibility. -/
theorem exists_restricted_Gamma0_lift (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    ∃ δ : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma0 (M * N) ∧
      (M : ℤ) ∣ δ 0 1 ∧ (δ 1 1 : ZMod N) = (γ 1 1 : ZMod N) := by
  have : NeZero N := ⟨hN.ne'⟩
  have : NeZero (M ^ 2 * N) := ⟨by positivity⟩
  have hd := diagonal_product_eq_one γ hγ
  let u : (ZMod N)ˣ := ⟨γ 1 1, γ 0 0, by simpa [mul_comm] using hd, hd⟩
  have hdiv : N ∣ M ^ 2 * N := dvd_mul_left _ _
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective hdiv u
  let a : ℤ := ((v⁻¹ : (ZMod (M ^ 2 * N))ˣ) : ZMod (M ^ 2 * N)).val
  let d : ℤ := (v : ZMod (M ^ 2 * N)).val
  have had : ((M ^ 2 * N : ℕ) : ℤ) ∣ a * d - 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simp only [a, d, Int.cast_sub, Int.cast_mul, Int.cast_one, Int.cast_natCast,
      ZMod.natCast_zmod_val, Units.inv_mul, sub_self]
  obtain ⟨t, ht⟩ := had
  let δ : SL(2, ℤ) := ⟨!![a, M; (M * N : ℕ) * t, d], by
    simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    push_cast at ht ⊢
    linear_combination ht⟩
  refine ⟨δ, ?_, ?_, ?_⟩
  · apply CongruenceSubgroup.Gamma0_mem.mpr
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    exact ⟨t, rfl⟩
  · exact dvd_refl _
  · have h := congrArg (fun w : (ZMod N)ˣ ↦ (w : ZMod N)) hv
    simpa only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_ofClass,
      ZMod.castHom_apply, ← ZMod.natCast_val, u, d, δ, Matrix.of_apply, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Int.cast_natCast] using h

/-- Two matrices in `Γ₀(N)` with the same bottom-right entry modulo `N`
differ by an element of `Γ₁(N)`. -/
theorem mul_inv_mem_Gamma1_of_lowerRight_eq {N : ℕ} (γ δ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (hδ : δ ∈ CongruenceSubgroup.Gamma0 N)
    (hd : (δ 1 1 : ZMod N) = (γ 1 1 : ZMod N)) :
    γ * δ⁻¹ ∈ CongruenceSubgroup.Gamma1 N := by
  have hγc := CongruenceSubgroup.Gamma0_mem.mp hγ
  have hδc := CongruenceSubgroup.Gamma0_mem.mp hδ
  have hγad := diagonal_product_eq_one γ hγ
  have hδad := diagonal_product_eq_one δ hδ
  apply (CongruenceSubgroup.Gamma1_mem N _).mpr
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Int.cast_add, Int.cast_mul, Int.cast_neg,
    hγc, hδc, hd, neg_zero, mul_zero, zero_mul, add_zero, zero_add]
  exact ⟨hγad, by simpa [hd, mul_comm] using hδad⟩

/-- A subgroup containing `Γ₁(N)` and every matrix with these off-diagonal
divisibilities contains `Γ₀(N)`. -/
theorem Gamma0_le_of_Gamma1_le_of_restricted {H : Subgroup SL(2, ℤ)}
    (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (h1 : CongruenceSubgroup.Gamma1 N ≤ H)
    (hrestricted : ∀ δ : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma0 (M * N) →
      (M : ℤ) ∣ δ 0 1 → δ ∈ H) : CongruenceSubgroup.Gamma0 N ≤ H := by
  intro γ hγ
  obtain ⟨δ, hδ, hb, hd⟩ := exists_restricted_Gamma0_lift N M hN hM γ hγ
  have hδN : δ ∈ CongruenceSubgroup.Gamma0 N := by
    apply CongruenceSubgroup.Gamma0_mem.mpr
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    exact dvd_trans (by exact_mod_cast dvd_mul_left N M)
      (Eta.level_dvd_lower_left (M * N) δ hδ)
  have hθ := h1 (mul_inv_mem_Gamma1_of_lowerRight_eq γ δ hγ hδN hd)
  have hm := H.mul_mem hθ (hrestricted δ hδ hb)
  simpa only [inv_mul_cancel_right] using hm

/-- Restricted off-diagonal invariance already supplies a principal
congruence subgroup, so the two Newman translations complete the descent. -/
theorem Gamma0_le_of_translations_of_restricted {H : Subgroup SL(2, ℤ)}
    (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (hT : ModularGroup.T ∈ H) (hL : lowerUnipotent N ∈ H)
    (hrestricted : ∀ δ : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma0 (M * N) →
      (M : ℤ) ∣ δ 0 1 → δ ∈ H) : CongruenceSubgroup.Gamma0 N ≤ H := by
  have hcong : CongruenceSubgroup.IsCongruenceSubgroup H := by
    refine ⟨M * N, Nat.mul_ne_zero hM.ne' hN.ne', ?_⟩
    intro δ hδ
    obtain ⟨_, hb, hc, _⟩ := CongruenceSubgroup.Gamma_mem.mp hδ
    apply hrestricted δ (CongruenceSubgroup.Gamma0_mem.mpr hc)
    have hb' := (ZMod.intCast_zmod_eq_zero_iff_dvd (δ 0 1) (M * N)).mp hb
    exact dvd_trans (by exact_mod_cast dvd_mul_right M N) hb'
  exact Gamma0_le_of_Gamma1_le_of_restricted N M hN hM
    (Gamma1_le_of_isCongruenceSubgroup N hcong hT hL) hrestricted

/-- The form of restricted-subgroup descent used by the eta-quotient proof. -/
theorem slash_Gamma0_of_Gamma1_of_restricted {f : ℍ → ℂ} {k : ℤ}
    (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (h1 : ∀ γ ∈ CongruenceSubgroup.Gamma1 N, f ∣[k] γ = f)
    (hrestricted : ∀ δ ∈ CongruenceSubgroup.Gamma0 (M * N),
      (M : ℤ) ∣ δ 0 1 → f ∣[k] δ = f)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) : f ∣[k] γ = f := by
  exact Gamma0_le_of_Gamma1_le_of_restricted (H := slashStabilizer f k)
    N M hN hM h1 hrestricted hγ

/-- To prove the full `Γ₀(N)` transformation law, it suffices to verify the
two Newman translations and matrices with these off-diagonal divisibilities.
No separate congruence-invariance hypothesis is needed. -/
theorem slash_Gamma0_of_translations_of_restricted {f : ℍ → ℂ} {k : ℤ}
    (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (hT : f ∣[k] ModularGroup.T = f) (hL : f ∣[k] lowerUnipotent N = f)
    (hrestricted : ∀ δ ∈ CongruenceSubgroup.Gamma0 (M * N),
      (M : ℤ) ∣ δ 0 1 → f ∣[k] δ = f)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) : f ∣[k] γ = f := by
  exact Gamma0_le_of_translations_of_restricted (H := slashStabilizer f k)
    N M hN hM hT hL hrestricted hγ

end WeightTwoCusps.EtaQuotient
