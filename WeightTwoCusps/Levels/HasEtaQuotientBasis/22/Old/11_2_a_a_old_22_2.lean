module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«11».New.«11_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# The dilation-2 lift of 11.2.a.a to level 22

This is the function `f(2z)`, where `f` is the level-11 newform.
Its eta product is the second element of the level-22 cuspidal basis in
`M2_Gamma0_Eta_Quotient_Bases_N_1_to_500`.
-/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The oldform `f(2z)` at level 22, with source `11.2.a.a`. -/
abbrev cuspForm_11_2_a_a_old_22_2 : gamma0CuspForms 22 :=
  gamma0Rescale cuspForm_11_2_a_a 2

/-- The degeneracy lift is the corresponding cuspidal eta product. -/
theorem cuspForm_11_2_a_a_old_22_2_eq_eta :
    cuspForm_11_2_a_a_old_22_2 =
      etaQuotientCuspForm 22 sparse![22; 1 => 2, 21 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_11_2_a_a_old_22_2_first_coeffs : first_coeffs 100 cuspForm_11_2_a_a_old_22_2 =
    [0, 0, 1, 0, -2, 0, -1, 0, 2, 0, 1, 0, 2, 0, -2, 0, 0, 0, -2, 0,
     -2, 0, 1, 0, -2, 0, 4, 0, 4, 0, -1, 0, -4, 0, -2, 0, 4, 0, 0, 0,
     2, 0, 2, 0, -2, 0, -1, 0, 0, 0, -4, 0, -8, 0, 5, 0, -4, 0, 0, 0,
     2, 0, 7, 0, 8, 0, -1, 0, 4, 0, -2, 0, -4, 0, 3, 0, 0, 0, -4, 0,
     0, 0, -8, 0, -4, 0, -6, 0, 2, 0, -2, 0, 2, 0, 8, 0, 4, 0, -3, 0] := by
  eta_coeff

end WeightTwoCusps
