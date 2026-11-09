module

public import WeightTwoCusps.EtaQuotient.Criteria.Necessary
public import WeightTwoCusps.EtaQuotient.Transformation.Basic

/-!
# The weight is forced by the exponent function

Comparing the eta-square multiplier law with the modular transformation law
at a nontrivial lower unipotent matrix determines the weight. This argument
works for arbitrary integer exponents, without a parity hypothesis.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Complex
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm

namespace WeightTwoCusps.EtaQuotient

private theorem lower_entries (N : ℕ) :
    lowerUnipotent N 1 0 = -(N : ℤ) ∧ lowerUnipotent N 1 1 = 1 := by
  simp only [lowerUnipotent, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.SL2_inv_expl, ModularGroup.coe_S, ModularGroup.coe_T_zpow,
    Matrix.mul_fin_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- A genuine modular form represented by an eta quotient has the expected weight. -/
theorem hasWeight_of_modularForm {N : ℕ} (hN : 0 < N) {r : Fin N → ℤ} {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (hf : (f : ℍ → ℂ) = etaQuotient N r) : HasWeight N r k := by
  let γ := lowerUnipotent N
  have hγ : γ ∈ CongruenceSubgroup.Gamma0 N := lowerUnipotent_mem N
  have hfγ := SlashInvariantForm.slash_action_eqn_SL'' f hγ UpperHalfPlane.I
  rw [hf] at hfγ
  have hs := square_transform N r γ hγ UpperHalfPlane.I
  rw [hfγ, mul_pow] at hs
  have hc : (denom γ UpperHalfPlane.I ^ k) ^ 2 =
      Eta.etaMultiplier (squareMultiplierExponent N r γ hγ) *
        denom γ UpperHalfPlane.I ^ exponentSum N r :=
    mul_right_cancel₀ (pow_ne_zero 2 (ne_zero N r UpperHalfPlane.I)) hs
  have hnorm (x : ZMod 12) : ‖Eta.etaMultiplier x‖ = 1 := (ZMod.toCircle x).norm_coe
  have hn := congrArg norm hc
  simp only [norm_pow, norm_mul, norm_zpow, hnorm, one_mul] at hn
  have hdenom : denom γ UpperHalfPlane.I = 1 - (N : ℂ) * I := by
    change (((lowerUnipotent N) 1 0 : ℤ) : ℂ) * I +
      ((lowerUnipotent N) 1 1 : ℤ) = _
    rw [(lower_entries N).1, (lower_entries N).2]
    push_cast
    ring
  have hsq : ‖denom γ UpperHalfPlane.I‖ ^ 2 = 1 + (N : ℝ) ^ 2 := by
    rw [hdenom, Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  have hgt : 1 < ‖denom γ UpperHalfPlane.I‖ := by
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    nlinarith [norm_nonneg (denom γ UpperHalfPlane.I)]
  have hp : ‖denom γ UpperHalfPlane.I‖ ^ (k * 2) =
      ‖denom γ UpperHalfPlane.I‖ ^ exponentSum N r := by
    simpa only [zpow_mul, zpow_ofNat] using hn
  have he := (zpow_right_strictMono₀ hgt).injective hp
  dsimp [HasWeight]
  omega

/-- The whole Newman package is necessary without assuming the weight in advance. -/
theorem newmanConditions_of_modularForm_autoWeight {N : ℕ} (hN : 0 < N)
    {r : Fin N → ℤ} {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (hf : (f : ℍ → ℂ) = etaQuotient N r) : NewmanConditions N r k :=
  newmanConditions_of_modularForm hN (hasWeight_of_modularForm hN f hf) f hf

end WeightTwoCusps.EtaQuotient
