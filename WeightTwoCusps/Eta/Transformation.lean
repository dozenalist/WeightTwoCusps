module

public import Mathlib.NumberTheory.ModularForms.Discriminant

/-! # The integral-weight transformation laws for the square of eta -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Function Complex
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm Real

namespace WeightTwoCusps.Eta

/-- The square of the Dedekind eta function has integral weight one. -/
def etaSq (z : ℍ) : ℂ := ModularForm.eta z ^ 2

private lemma csqrt_sq (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  exact Complex.cpow_ofNat_inv_pow z 2

/-- Eta squared transforms under inversion with the factor `-I * z`. -/
theorem eta_sq_S_smul (z : ℍ) :
    ModularForm.eta (ModularGroup.S • z : ℍ) ^ 2 =
      (-I * (z : ℂ)) * ModularForm.eta z ^ 2 := by
  have h := ModularForm.eta_comp_eq_csqrt_I_inv z.2
  simp only [Function.comp_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at h
  have he : ModularForm.eta (ModularGroup.S • z : ℍ) =
      (Complex.sqrt I)⁻¹ * (Complex.sqrt (z : ℂ) * ModularForm.eta z) := by
    rw [modular_S_smul]
    simpa only [UpperHalfPlane.coe_mk, neg_div, one_div, inv_neg] using h
  rw [he, mul_pow, mul_pow, inv_pow, csqrt_sq, csqrt_sq]
  simp [Complex.inv_I, mul_assoc]

/-- The weight-one slash action of `S` on eta squared is multiplication by `-I`. -/
theorem etaSq_slash_S : etaSq ∣[(1 : ℤ)] ModularGroup.S = (-I) • etaSq := by
  ext z
  rw [ModularForm.SL_slash_apply]
  simp only [etaSq, eta_sq_S_smul,
    ModularGroup.denom_S, Pi.smul_apply, smul_eq_mul, Int.reduceNeg, zpow_neg_one]
  field_simp [z.ne_zero]

/-- The unit complex number occurring in the translation law for eta squared. -/
def etaSqTMultiplier : ℂ := Complex.exp (π * I / 6)

private theorem qParam_one_add_one (z : ℂ) :
    Periodic.qParam 1 (z + 1) = Periodic.qParam 1 z := by
  simp only [Periodic.qParam, Complex.ofReal_one, div_one]
  rw [mul_add, mul_one, Complex.exp_periodic]

/-- The translation transformation of eta squared, before taking the slash action. -/
theorem eta_sq_add_one (z : ℂ) :
    ModularForm.eta (z + 1) ^ 2 = etaSqTMultiplier * ModularForm.eta z ^ 2 := by
  simp only [ModularForm.eta, mul_pow, ModularForm.eta_q, qParam_one_add_one]
  rw [show Periodic.qParam 24 (z + 1) ^ 2 =
      etaSqTMultiplier * Periodic.qParam 24 z ^ 2 by
    simp only [Periodic.qParam, etaSqTMultiplier, ← Complex.exp_nat_mul,
      Nat.cast_ofNat, Complex.ofReal_ofNat, ← Complex.exp_add]
    congr 1
    ring]
  ring

/-- The weight-one slash action of `T` on eta squared. -/
theorem etaSq_slash_T :
    etaSq ∣[(1 : ℤ)] ModularGroup.T = etaSqTMultiplier • etaSq := by
  ext z
  rw [ModularForm.SL_slash_apply]
  rw [show denom ModularGroup.T z = 1 by
    simp [ModularGroup.denom_apply, ModularGroup.T]]
  simp only [etaSq, modular_T_smul, UpperHalfPlane.coe_vadd, Complex.ofReal_one]
  simpa [add_comm, etaSq] using eta_sq_add_one (z : ℂ)

end WeightTwoCusps.Eta
