module

public import WeightTwoCusps.Eta.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-! # Integral level conjugation and its compatibility with dilation -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Complex
open UpperHalfPlane hiding I
open scoped MatrixGroups

namespace WeightTwoCusps.Eta

theorem level_dvd_lower_left (N : ℕ) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) : (N : ℤ) ∣ γ 1 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp (CongruenceSubgroup.Gamma0_mem.mp hγ)

theorem lower_left_div_mul (N : ℕ) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) : γ 1 0 / N * N = γ 1 0 :=
  Int.ediv_mul_cancel (level_dvd_lower_left N γ hγ)

/-- Conjugation by `diag(N,1)` is integral on `Γ₀(N)`. -/
def levelConjugate (N : ℕ) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    SL(2, ℤ) :=
  ⟨!![γ 0 0, N * γ 0 1; γ 1 0 / N, γ 1 1], by
    rw [Matrix.det_fin_two_of]
    calc γ 0 0 * γ 1 1 - (N * γ 0 1) * (γ 1 0 / N)
        = γ 0 0 * γ 1 1 - γ 0 1 * (γ 1 0 / N * N) := by ring
      _ = γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 := by rw [lower_left_div_mul N γ hγ]
      _ = 1 := by simpa only [Matrix.det_fin_two] using γ.det_coe⟩

theorem denom_levelConjugate (N : ℕ) (hN : 0 < N) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (z : ℍ) :
    denom (levelConjugate N γ hγ) (dilate N (by exact_mod_cast hN) z) = denom γ z := by
  change ((γ 1 0 / N : ℤ) : ℂ) * ((N : ℂ) * (z : ℂ)) + γ 1 1 =
    (γ 1 0 : ℂ) * z + γ 1 1
  have hc : ((γ 1 0 / N : ℤ) : ℂ) * N = γ 1 0 := by
    exact_mod_cast lower_left_div_mul N γ hγ
  rw [← mul_assoc, hc]

/-- Positive integral dilation intertwines a matrix and its level conjugate. -/
theorem dilate_smul (N : ℕ) (hN : 0 < N) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (z : ℍ) :
    dilate N (by exact_mod_cast hN) (γ • z) =
      levelConjugate N γ hγ • dilate N (by exact_mod_cast hN) z := by
  apply UpperHalfPlane.ext
  simp only [coe_dilate, Complex.ofReal_natCast, coe_specialLinearGroup_apply]
  have hc : ((γ 1 0 / (N : ℤ) : ℤ) : ℂ) * N = γ 1 0 := by
    exact_mod_cast lower_left_div_mul N γ hγ
  have hd : ((γ 1 0 / (N : ℤ) : ℤ) : ℂ) * ((N : ℂ) * (z : ℂ)) + γ 1 1 =
      (γ 1 0 : ℂ) * z + γ 1 1 := by rw [← mul_assoc, hc]
  change (N : ℂ) * (((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)) =
    (((γ 0 0 : ℂ) * ((N : ℂ) * z) + ((N : ℤ) * γ 0 1 : ℤ)) /
      (((γ 1 0 / (N : ℤ) : ℤ) : ℂ) * ((N : ℂ) * z) + γ 1 1))
  rw [hd]
  push_cast
  ring

end WeightTwoCusps.Eta
