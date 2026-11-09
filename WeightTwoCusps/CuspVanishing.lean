module

public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.Algebra.Field.ZMod

/-! # A two-cusp criterion for prime-level modular forms -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open UpperHalfPlane Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

namespace WeightTwoCusps

/-- At prime level it suffices to check vanishing at `∞` and `0`.
This applies to any weight and any slash-invariant function, without holomorphy. -/
theorem zero_at_cusps_Gamma0_prime (p : ℕ) [Fact p.Prime] {f : ℍ → ℂ} {k : ℤ}
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma0 p, f ∣[k] γ = f)
    (hInfty : IsZeroAtImInfty f) (h₀ : IsZeroAtImInfty (f ∣[k] ModularGroup.S))
    {c : OnePoint ℝ} (hc : IsCusp c (CongruenceSubgroup.Gamma0 p)) :
    c.IsZeroAt f k := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
  intro γ _
  by_cases hγ : (γ 1 0 : ZMod p) = 0
  · rw [hinv γ (CongruenceSubgroup.Gamma0_mem.mpr hγ)]
    exact hInfty
  · let n : ℤ := ((γ 1 1 : ZMod p) / (γ 1 0 : ZMod p)).val
    let δ := γ * (ModularGroup.S * ModularGroup.T ^ n)⁻¹
    have hδ : δ ∈ CongruenceSubgroup.Gamma0 p := by
      rw [CongruenceSubgroup.Gamma0_mem]
      simp only [δ, coe_mul, SL2_inv_expl, ModularGroup.coe_S,
        ModularGroup.coe_T_zpow, Matrix.mul_fin_two]
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, mul_zero, zero_mul, one_mul, mul_one,
        zero_add, add_zero, neg_neg]
      push_cast
      simp only [n, Int.cast_natCast, ZMod.natCast_zmod_val]
      field_simp
      ring
    have heq : γ = δ * (ModularGroup.S * ModularGroup.T ^ n) := by
      simp only [δ, mul_assoc, inv_mul_cancel, mul_one]
    rw [heq, SlashAction.slash_mul, hinv δ hδ, SlashAction.slash_mul]
    rw [ModularForm.SL_slash]
    exact h₀.slash k (by
      change (((ModularGroup.T ^ n) 1 0 : ℤ) : ℝ) = 0
      simp [ModularGroup.coe_T_zpow])

end WeightTwoCusps
