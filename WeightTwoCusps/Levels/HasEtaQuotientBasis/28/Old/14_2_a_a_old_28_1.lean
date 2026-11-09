module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«14».New.«14_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# The dilation-1 lift of 14.2.a.a to level 28

This is the function `f(z)`, where `f` is the level-14 newform.
Its eta product is the first element of the level-28 cuspidal basis in
`M2_Gamma0_Eta_Quotient_Bases_N_1_to_500`.
-/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The oldform `f(z)` at level 28, with source `14.2.a.a`. -/
abbrev cuspForm_14_2_a_a_old_28_1 : gamma0CuspForms 28 :=
  gamma0RescaleToLevel cuspForm_14_2_a_a 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta product. -/
theorem cuspForm_14_2_a_a_old_28_1_eq_eta :
    cuspForm_14_2_a_a_old_28_1 =
      etaQuotientCuspForm 28 sparse![28; 0 => 1, 1 => 1, 6 => 1, 13 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_14_2_a_a_old_28_1_first_coeffs : first_coeffs 100 cuspForm_14_2_a_a_old_28_1 =
    [0, 1, -1, -2, 1, 0, 2, 1, -1, 1, 0, 0, -2, -4, -1, 0, 1, 6, -1, 2,
     0, -2, 0, 0, 2, -5, 4, 4, 1, -6, 0, -4, -1, 0, -6, 0, 1, 2, -2, 8,
     0, 6, 2, 8, 0, 0, 0, -12, -2, 1, 5, -12, -4, 6, -4, 0, -1, -4, 6, -6,
     0, 8, 4, 1, 1, 0, 0, -4, 6, 0, 0, 0, -1, 2, -2, 10, 2, 0, -8, 8,
     0, -11, -6, -6, -2, 0, -8, 12, 0, -6, 0, -4, 0, 8, 12, 0, 2, -10, -1, 0] := by
  eta_coeff

end WeightTwoCusps
