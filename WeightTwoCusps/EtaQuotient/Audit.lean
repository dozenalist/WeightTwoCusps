module

import WeightTwoCusps.EtaQuotient
import WeightTwoCusps.EtaQuotient.Examples

/-! # Axiom audit and public-interface verification for eta quotients -/

#print axioms WeightTwoCusps.EtaQuotient.ne_zero
#print axioms WeightTwoCusps.EtaQuotient.holo
#print axioms WeightTwoCusps.EtaQuotient.slash_T_eq_self_iff
#print axioms WeightTwoCusps.EtaQuotient.slash_lower_eq_self_iff
#print axioms WeightTwoCusps.EtaQuotient.newmanConditions_of_modularForm
#print axioms WeightTwoCusps.EtaQuotient.even_weight_of_modularForm
#print axioms WeightTwoCusps.EtaQuotient.isBoundedAtImInfty_iff
#print axioms WeightTwoCusps.EtaQuotient.isZeroAtImInfty_iff
#print axioms WeightTwoCusps.EtaQuotient.slash_S_isBoundedAtImInfty_iff
#print axioms WeightTwoCusps.EtaQuotient.slash_Gamma0_of_evenExponents
#print axioms WeightTwoCusps.EtaQuotient.hasWeight_of_modularForm
#print axioms WeightTwoCusps.EtaQuotient.newmanConditions_of_modularForm_autoWeight
#print axioms WeightTwoCusps.EtaQuotient.Examples.negativeLevelElevenForm
#print axioms WeightTwoCusps.EtaQuotient.Examples.levelFourteenForm
#print axioms WeightTwoCusps.EtaQuotient.exists_cusp_factorization
#print axioms WeightTwoCusps.EtaQuotient.etaSq_dilate_slash_eq_affine
#print axioms WeightTwoCusps.EtaQuotient.cuspUnit_tendsto_nonzero
#print axioms WeightTwoCusps.EtaQuotient.slash_isBounded_iff
#print axioms WeightTwoCusps.EtaQuotient.slash_isZero_iff
#print axioms WeightTwoCusps.EtaQuotient.even_newman_ligozat_iff
#print axioms WeightTwoCusps.EtaQuotient.even_cuspidal_newman_ligozat_iff
#print axioms WeightTwoCusps.EtaQuotient.multiplierCharacter
#print axioms WeightTwoCusps.EtaQuotient.slashMultiplier_eq_one_or_neg_one
#print axioms WeightTwoCusps.EtaQuotient.qExpansion_eq_X_pow_mul
#print axioms WeightTwoCusps.EtaQuotient.qExpansion_order
#print axioms WeightTwoCusps.EtaQuotient.cuspOrder_eq_qExpansion_order
#print axioms WeightTwoCusps.EtaQuotient.cuspOrder_integral_of_modularForm
#print axioms WeightTwoCusps.EtaQuotient.Gamma1_le_of_isCongruenceSubgroup
#print axioms WeightTwoCusps.EtaQuotient.Examples.exists_levelFour_form
#print axioms WeightTwoCusps.EtaQuotient.Examples.levelFifteen_conditions
#print axioms WeightTwoCusps.EtaQuotient.qExpansion_eulerFactor_coeff
#print axioms WeightTwoCusps.EtaQuotient.eulerCoefficient_cast
#print axioms WeightTwoCusps.EtaQuotient.qExpansion_coeff_leading_add_one
#print axioms WeightTwoCusps.EtaQuotient.qExpansion_coeff_leading_add_two
#print axioms WeightTwoCusps.EtaQuotient.qExpansion_eulerFactorPower_coeff
#print axioms WeightTwoCusps.EtaQuotient.qExpansion_unitPart_coeff
#print axioms WeightTwoCusps.EtaQuotient.qExpansion_coeff_eq_coefficient
#print axioms WeightTwoCusps.EtaQuotient.qExpansion_coeff_integral
#print axioms WeightTwoCusps.EtaQuotient.qExpansion_coeff_im
#print axioms WeightTwoCusps.EtaQuotient.qExpansion_coeff_mul_of_exponent_add
#print axioms WeightTwoCusps.etaQuotientMF_qExpansion_coeff
#print axioms WeightTwoCusps.etaQuotientCuspForm_qExpansion_coeff
#print axioms WeightTwoCusps.EtaQuotient.Examples.levelFour_cusp_half_qExpansion_order
#print axioms WeightTwoCusps.EtaQuotient.eta_half_transform
#print axioms WeightTwoCusps.EtaQuotient.halfMultiplier_pow_twentyFour
#print axioms WeightTwoCusps.EtaQuotient.halfDenom_mul
#print axioms WeightTwoCusps.EtaQuotient.halfCocycle_eq_one_or_neg_one
#print axioms WeightTwoCusps.EtaQuotient.slashMultiplier_eq_prod_halfMultiplier
#print axioms WeightTwoCusps.EtaQuotient.Gamma0_four_eq_closure
#print axioms WeightTwoCusps.EtaQuotient.halfCocycle_eq_entry_sign
#print axioms WeightTwoCusps.EtaQuotient.extendedJacobi.congr_right
#print axioms WeightTwoCusps.EtaQuotient.extendedJacobi_lower_four
#print axioms WeightTwoCusps.EtaQuotient.matrixMultiplierExponent_lowerTranslation_four
#print axioms WeightTwoCusps.EtaQuotient.arithmeticHalfMultiplier_neg
#print axioms WeightTwoCusps.EtaQuotient.halfMultiplier_eq_extendedJacobi
#print axioms WeightTwoCusps.EtaQuotient.exists_restricted_Gamma0_lift
#print axioms WeightTwoCusps.EtaQuotient.Gamma0_le_of_translations_of_restricted
#print axioms WeightTwoCusps.EtaQuotient.prod_extendedJacobi_zpow_eq_one_of_isSquare
#print axioms WeightTwoCusps.EtaQuotient.slash_Gamma0_of_newman_trivialCharacter
#print axioms WeightTwoCusps.etaQuotientMF
#print axioms WeightTwoCusps.etaQuotientCuspForm
#print axioms WeightTwoCusps.EtaQuotient.Examples.levelFifteenForm
#print axioms WeightTwoCusps.EtaQuotient.Examples.signedLevelFifteenCuspForm

open WeightTwoCusps
open WeightTwoCusps.EtaQuotient
open UpperHalfPlane

noncomputable section

-- Check the public interface printed in EtaQuotient/README.md.
example (N : ℕ) (hN : 0 < N) (r : Fin N → ℤ) (k : ℤ) (hr : EvenExponents N r) :
    (∃ f : ModularForm (CongruenceSubgroup.Gamma0 N) k,
      (f : ℍ → ℂ) = etaQuotient N r) ↔ NewmanLigozatConditions N r k :=
  even_newman_ligozat_iff N hN r k hr

example : NewmanLigozatConditions 4 Examples.levelFour 2 := by decide +kernel

example : NewmanLigozatConditions 15 Examples.levelFifteen 2 := by decide +kernel

example : ModularForm (CongruenceSubgroup.Gamma0 15) 2 :=
  etaQuotientMF 15 Examples.levelFifteen

example : CuspForm (CongruenceSubgroup.Gamma0 15) 4 :=
  etaQuotientCuspForm 15 Examples.signedLevelFifteen

-- Either proof can still be supplied while the other is discharged automatically.
example : CuspForm (CongruenceSubgroup.Gamma0 15) 2 :=
  etaQuotientCuspForm 15 Examples.levelFifteen Examples.levelFifteen_conditions

example : CuspForm (CongruenceSubgroup.Gamma0 15) 2 :=
  etaQuotientCuspForm 15 Examples.levelFifteen (hc := Examples.levelFifteen_vanishing)

example := etaQuotientMF 15 Examples.levelFifteen (k := 2)

-- General constructors replace the former prime-level and paired-product constructions.
example : CuspForm (CongruenceSubgroup.Gamma0 23) 2 :=
  etaQuotientCuspForm 23 (fun i ↦ if i = 0 ∨ i = 22 then 2 else 0)

example : CuspForm (CongruenceSubgroup.Gamma0 35) 2 :=
  etaQuotientCuspForm 35 (fun i ↦ if i = 0 ∨ i = 34 then 2 else 0)
