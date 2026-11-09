module

public import WeightTwoCusps.Eta.Transformation
public import WeightTwoCusps.Eta.Exponent
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-! # The eta-square character on the integral modular group -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Function Complex
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm Real

namespace WeightTwoCusps.Eta

/-- The twelfth roots of unity, as an additive character. -/
def etaMultiplier : AddChar (ZMod 12) ℂ := ZMod.stdAddChar

@[simp] theorem etaMultiplier_ne_zero (x : ZMod 12) : etaMultiplier x ≠ 0 := by
  exact (ZMod.toCircle x).coe_ne_zero

@[simp] theorem etaMultiplier_one : etaMultiplier 1 = etaSqTMultiplier := by
  rw [etaMultiplier, show (1 : ZMod 12) = ((1 : ℤ) : ZMod 12) by rfl,
    ZMod.stdAddChar_coe]
  congr 1
  simp only [Int.cast_one, mul_one]
  ring

@[simp] theorem etaMultiplier_neg_three : etaMultiplier (-3) = -I := by
  rw [etaMultiplier, show (-3 : ZMod 12) = ((-3 : ℤ) : ZMod 12) by norm_num,
    ZMod.stdAddChar_coe]
  push_cast
  rw [show 2 * (π : ℂ) * I * -3 / 12 = -(π : ℂ) / 2 * I by ring]
  exact Complex.exp_neg_pi_div_two_mul_I

/-- The exponent of the eta-square character is additive under matrix multiplication. -/
theorem etaExponent_mul (γ δ : SL(2, ℤ)) :
    etaExponent (γ * δ) = etaExponent γ + etaExponent δ := by
  have hδ : δ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hδ using Subgroup.closure_induction_right with
  | one => simp
  | mul_right x hx y hy ih =>
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · rw [← mul_assoc, etaExponent_mul_S, etaExponent_mul_S, ih]
      ring
    · obtain rfl := Set.mem_singleton_iff.mp hy
      rw [← mul_assoc, etaExponent_mul_T, etaExponent_mul_T, ih]
      ring
  | mul_inv_cancel x hx y hy ih =>
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · have h₁ := etaExponent_mul_S (γ * (x * ModularGroup.S⁻¹))
      have h₂ := etaExponent_mul_S (x * ModularGroup.S⁻¹)
      simp only [mul_assoc, inv_mul_cancel, mul_one] at h₁ h₂
      linear_combination ih - h₁ + h₂
    · obtain rfl := Set.mem_singleton_iff.mp hy
      have h₁ := etaExponent_mul_T (γ * (x * ModularGroup.T⁻¹))
      have h₂ := etaExponent_mul_T (x * ModularGroup.T⁻¹)
      simp only [mul_assoc, inv_mul_cancel, mul_one] at h₁ h₂
      linear_combination ih - h₁ + h₂

@[simp] theorem etaExponent_inv (γ : SL(2, ℤ)) :
    etaExponent γ⁻¹ = -etaExponent γ := by
  have h := etaExponent_mul γ γ⁻¹
  simp only [mul_inv_cancel, etaExponent_one] at h
  linear_combination -h

/-- The weight-one transformation of eta squared under every integral modular matrix. -/
theorem etaSq_slash (γ : SL(2, ℤ)) :
    etaSq ∣[(1 : ℤ)] γ = etaMultiplier (etaExponent γ) • etaSq := by
  have hγ : γ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hγ using Subgroup.closure_induction with
  | one => simp
  | mem g hg =>
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · simpa using etaSq_slash_S
    · obtain rfl := Set.mem_singleton_iff.mp hg
      simpa using etaSq_slash_T
  | mul g h hg hh ihg ihh =>
    rw [SlashAction.slash_mul, ihg, ModularForm.SL_smul_slash, ihh,
      smul_smul, etaExponent_mul, AddChar.map_add_eq_mul]
  | inv g hg ih =>
    have h := congrArg (fun f : ℍ → ℂ ↦ f ∣[(1 : ℤ)] g⁻¹) ih
    simp only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one,
      ModularForm.SL_smul_slash] at h
    rw [etaExponent_inv, AddChar.map_neg_eq_inv]
    have h' := congrArg (fun f : ℍ → ℂ ↦
      (etaMultiplier (etaExponent g))⁻¹ • f) h
    simpa [← smul_smul] using h'.symm

/-- The pointwise eta-square transformation, with its twelfth-root multiplier. -/
theorem etaSq_modular_transform (γ : SL(2, ℤ)) (z : ℍ) :
    etaSq (γ • z) = etaMultiplier (etaExponent γ) * denom γ z * etaSq z := by
  have h := congrFun (etaSq_slash γ) z
  simp only [ModularForm.SL_slash_apply, Int.reduceNeg, zpow_neg_one,
    Pi.smul_apply, smul_eq_mul] at h
  have hd := denom_ne_zero γ z
  field_simp at h ⊢
  linear_combination h

end WeightTwoCusps.Eta
