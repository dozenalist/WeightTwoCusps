module

public import WeightTwoCusps.EtaQuotient.QExpansion.Computable
public import WeightTwoCusps.EtaQuotient.Cusps.Order
public import WeightTwoCusps.EtaQuotient.Constructor

/-! # Checked examples, including negative exponents and composite levels -/

@[expose] public section

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace WeightTwoCusps.EtaQuotient.Examples

/-- At level one the finite input has exactly one exponent. -/
def levelOne : Fin 1 → ℤ := ![24]

theorem levelOne_conditions : NewmanLigozatConditions 1 levelOne 12 := by decide +kernel

theorem levelOne_apply (z : ℍ) : etaQuotient 1 levelOne z = ModularForm.discriminant z := by
  simp [etaQuotient, exponent, levelOne, ModularForm.discriminant]

theorem levelOne_qExpansion_order :
    (UpperHalfPlane.qExpansion 1 (etaQuotient 1 levelOne)).order = 1 :=
  qExpansion_order (v := 1) (by decide +kernel)

/-- Exponents for `η(z)² η(11z)²`. -/
def levelEleven : Fin 11 → ℤ := ![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]

/-- The classical level-eleven form, constructed through the finite-function API. -/
def levelElevenForm : CuspForm (CongruenceSubgroup.Gamma0 11) 2 :=
  etaQuotientCuspForm 11 levelEleven

theorem levelEleven_weight : HasWeight 11 levelEleven 2 := by
  unfold HasWeight
  decide +kernel

theorem levelEleven_apply (z : ℍ) :
    etaQuotient 11 levelEleven z = ModularForm.eta z ^ 2 * ModularForm.eta (11 * (z : ℂ)) ^ 2 := by
  norm_num [etaQuotient, levelEleven, exponent,
    Nat.Prime.divisors (by decide : Nat.Prime 11)]

/-- Exponents for the holomorphic eta quotient `η(11z)^22 / η(z)^2`. -/
def negativeLevelEleven : Fin 11 → ℤ := ![-2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22]

/-- A genuine modular form with a negative exponent. -/
def negativeLevelElevenForm :
    ModularForm (CongruenceSubgroup.Gamma0 11) 10 :=
  etaQuotientMF 11 negativeLevelEleven

theorem negativeLevelEleven_weight : HasWeight 11 negativeLevelEleven 10 := by
  unfold HasWeight
  decide +kernel

theorem negativeLevelEleven_cusp_zero_order : zeroSum 11 negativeLevelEleven = 0 := by
  decide +kernel

/-- Exponents for `η(z)² η(2z)² η(7z)² η(14z)²`. -/
def levelFourteen : Fin 14 → ℤ := ![2, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2]

/-- A modular eta product at a composite level divisible by two. -/
def levelFourteenForm :
    ModularForm (CongruenceSubgroup.Gamma0 14) 4 :=
  etaQuotientMF 14 levelFourteen

theorem levelFourteen_weight : HasWeight 14 levelFourteen 4 := by
  unfold HasWeight
  decide +kernel

/-- A signed exponent function at composite level, representing the fourth power of theta. -/
def levelFour : Fin 4 → ℤ := ![-8, 20, 0, -8]

theorem levelFour_conditions : NewmanLigozatConditions 4 levelFour 2 := by decide +kernel

/-- The general even criterion handles cancellation at the intermediate cusp `1/2`. -/
theorem exists_levelFour_form :
    ∃ f : ModularForm (CongruenceSubgroup.Gamma0 4) 2,
      (f : ℍ → ℂ) = etaQuotient 4 levelFour :=
  ⟨etaQuotientMF 4 levelFour, rfl⟩

theorem levelFour_intermediate_cusp : cuspSum 4 levelFour 2 = 24 := by decide +kernel

theorem levelFour_qExpansion_coeff_zero :
    (UpperHalfPlane.qExpansion 1 (etaQuotient 4 levelFour)).coeff 0 = 1 :=
  qExpansion_coeff_leading (v := 0) (by decide +kernel)

theorem levelFour_qExpansion_coeff_one :
    (UpperHalfPlane.qExpansion 1 (etaQuotient 4 levelFour)).coeff 1 = 8 := by
  rw [qExpansion_coeff_leading_add_one (v := 0) (by decide +kernel)]
  norm_num [exponent, levelFour]

def levelFourHalfMatrix : SL(2, ℤ) := ⟨!![1, 0; 2, 1], by decide⟩

theorem levelFour_cusp_half_qExpansion_order :
    (UpperHalfPlane.qExpansion (cuspWidth 4 2 : ℝ)
      (etaQuotient 4 levelFour ∣[(2 : ℤ)] levelFourHalfMatrix)).order = 1 := by
  obtain ⟨f, hf⟩ := exists_levelFour_form
  obtain ⟨n, hn, horder⟩ := cuspOrder_eq_qExpansion_order (by decide : 0 < 4)
    (by decide : 2 ∈ (4 : ℕ).divisors) f hf
    levelFourHalfMatrix (by decide +kernel)
  have hc : cuspOrder 4 levelFour 2 = 1 := by decide +kernel
  rw [hc] at horder
  have hn1 : n = 1 := by exact_mod_cast horder.symm
  simpa only [hn1, Nat.cast_one] using hn

theorem levelEleven_qExpansion_order :
    (UpperHalfPlane.qExpansion 1 (etaQuotient 11 levelEleven)).order = 1 :=
  qExpansion_order (v := 1) (by decide +kernel)

theorem negativeLevelEleven_qExpansion_order :
    (UpperHalfPlane.qExpansion 1 (etaQuotient 11 negativeLevelEleven)).order = 10 :=
  qExpansion_order (v := 10) (by decide +kernel)

theorem negativeLevelEleven_qExpansion_coeff_eleven :
    (UpperHalfPlane.qExpansion 1 (etaQuotient 11 negativeLevelEleven)).coeff 11 = 2 := by
  rw [qExpansion_coeff_leading_add_one (v := 10) (by decide +kernel)]
  norm_num [exponent, negativeLevelEleven]

/-- The classical odd-exponent level-fifteen product. -/
def levelFifteen : Fin 15 → ℤ := ![1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

theorem levelFifteen_conditions : NewmanLigozatConditions 15 levelFifteen 2 := by
  have hd : (15 : ℕ).divisors = {1, 3, 5, 15} := by decide
  refine ⟨⟨by norm_num, ?_, ?_, ?_⟩, ⟨by norm_num, ⟨15, ?_⟩⟩, ?_⟩
  all_goals
    norm_num [HasWeight, exponentSum, infinitySum, zeroSum, characterProduct,
      HolomorphicAtCusps, cuspSum, hd, exponent, levelFifteen]

theorem levelFifteen_vanishing : VanishingAtCusps 15 levelFifteen := by decide +kernel

theorem levelFifteen_not_even : ¬EvenExponents 15 levelFifteen := by decide +kernel

/-- Odd exponents are accepted, with the arithmetic proof discharged automatically. -/
def levelFifteenForm : ModularForm (CongruenceSubgroup.Gamma0 15) 2 :=
  etaQuotientMF 15 levelFifteen

def levelFifteenCuspForm : CuspForm (CongruenceSubgroup.Gamma0 15) 2 :=
  etaQuotientCuspForm 15 levelFifteen

theorem levelFifteenForm_apply (z : ℍ) :
    levelFifteenForm z = etaQuotient 15 levelFifteen z := rfl

/-- A signed, odd-exponent cusp form: `η(3z)^5 η(5z)^5 / (η(z) η(15z))`. -/
def signedLevelFifteen : Fin 15 → ℤ := ![-1, 0, 5, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]

theorem signedLevelFifteen_conditions : NewmanLigozatConditions 15 signedLevelFifteen 4 := by
  decide +kernel

theorem signedLevelFifteen_not_even : ¬EvenExponents 15 signedLevelFifteen := by decide +kernel

def signedLevelFifteenForm : ModularForm (CongruenceSubgroup.Gamma0 15) 4 :=
  etaQuotientMF 15 signedLevelFifteen

def signedLevelFifteenCuspForm : CuspForm (CongruenceSubgroup.Gamma0 15) 4 :=
  etaQuotientCuspForm 15 signedLevelFifteen

theorem signedLevelFifteen_qExpansion_order :
    (UpperHalfPlane.qExpansion 1 (etaQuotient 15 signedLevelFifteen)).order = 1 :=
  qExpansion_order (v := 1) (by decide +kernel)

theorem signedLevelFifteen_qExpansion_coeff_two :
    (UpperHalfPlane.qExpansion 1 (etaQuotient 15 signedLevelFifteen)).coeff 2 = 1 := by
  rw [qExpansion_coeff_leading_add_one (v := 1) (by decide +kernel)]
  norm_num [exponent, signedLevelFifteen]

theorem levelFifteen_qExpansion_order :
    (UpperHalfPlane.qExpansion 1 (etaQuotient 15 levelFifteen)).order = 1 :=
  qExpansion_order (v := 1) (by decide +kernel)

theorem levelFifteen_qExpansion_coeff_two :
    (UpperHalfPlane.qExpansion 1 (etaQuotient 15 levelFifteen)).coeff 2 = -1 := by
  rw [qExpansion_coeff_leading_add_one (v := 1) (by decide +kernel)]
  norm_num [exponent, levelFifteen]

/-- The translation congruence rules out eta itself at this level in every integral weight. -/
theorem eta_not_level_eleven (k : ℤ) :
    ¬∃ f : ModularForm (CongruenceSubgroup.Gamma0 11) k,
      (f : ℍ → ℂ) = etaQuotient 11 (fun i ↦ if i = 0 then 1 else 0) := by
  rintro ⟨f, hf⟩
  have hc := infinitySum_dvd_of_modularForm f hf
  exact (by decide +kernel :
    ¬ (24 : ℤ) ∣ infinitySum 11 (fun i ↦ if i = 0 then 1 else 0)) hc

end WeightTwoCusps.EtaQuotient.Examples
