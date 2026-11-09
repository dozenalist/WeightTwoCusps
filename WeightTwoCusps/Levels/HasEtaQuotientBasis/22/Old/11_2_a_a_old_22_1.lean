module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«11».New.«11_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# The dilation-1 lift of 11.2.a.a to level 22

This is the function `f(z)`, where `f` is the level-11 newform.
Its eta product is the first element of the level-22 cuspidal basis in
`M2_Gamma0_Eta_Quotient_Bases_N_1_to_500`.
-/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The oldform `f(z)` at level 22, with source `11.2.a.a`. -/
abbrev cuspForm_11_2_a_a_old_22_1 : gamma0CuspForms 22 :=
  gamma0RescaleToLevel cuspForm_11_2_a_a 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta product. -/
theorem cuspForm_11_2_a_a_old_22_1_eq_eta :
    cuspForm_11_2_a_a_old_22_1 =
      etaQuotientCuspForm 22 sparse![22; 0 => 2, 10 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_11_2_a_a_old_22_1_first_coeffs : first_coeffs 100 cuspForm_11_2_a_a_old_22_1 =
    [0, 1, -2, -1, 2, 1, 2, -2, 0, -2, -2, 1, -2, 4, 4, -1, -4, -2, 4, 0,
     2, 2, -2, -1, 0, -4, -8, 5, -4, 0, 2, 7, 8, -1, 4, -2, -4, 3, 0, -4,
     0, -8, -4, -6, 2, -2, 2, 8, 4, -3, 8, 2, 8, -6, -10, 1, 0, 0, 0, 5,
     -2, 12, -14, 4, -8, 4, 2, -7, -4, 1, 4, -3, 0, 4, -6, 4, 0, -2, 8, -10,
     -4, 1, 16, -6, 4, -2, 12, 0, 0, 15, 4, -8, -2, -7, -16, 0, -8, -7, 6, -2] := by
  eta_coeff

end WeightTwoCusps
