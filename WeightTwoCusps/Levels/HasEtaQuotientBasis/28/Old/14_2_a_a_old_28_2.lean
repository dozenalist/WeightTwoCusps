module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«14».New.«14_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# The dilation-2 lift of 14.2.a.a to level 28

This is the function `f(2z)`, where `f` is the level-14 newform.
Its eta product is the second element of the level-28 cuspidal basis in
`M2_Gamma0_Eta_Quotient_Bases_N_1_to_500`.
-/

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The oldform `f(2z)` at level 28, with source `14.2.a.a`. -/
abbrev cuspForm_14_2_a_a_old_28_2 : gamma0CuspForms 28 :=
  gamma0Rescale cuspForm_14_2_a_a 2

/-- The degeneracy lift is the corresponding cuspidal eta product. -/
theorem cuspForm_14_2_a_a_old_28_2_eq_eta :
    cuspForm_14_2_a_a_old_28_2 =
      etaQuotientCuspForm 28 sparse![28; 1 => 1, 3 => 1, 13 => 1, 27 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_14_2_a_a_old_28_2_first_coeffs : first_coeffs 100 cuspForm_14_2_a_a_old_28_2 =
    [0, 0, 1, 0, -1, 0, -2, 0, 1, 0, 0, 0, 2, 0, 1, 0, -1, 0, 1, 0,
     0, 0, 0, 0, -2, 0, -4, 0, -1, 0, 0, 0, 1, 0, 6, 0, -1, 0, 2, 0,
     0, 0, -2, 0, 0, 0, 0, 0, 2, 0, -5, 0, 4, 0, 4, 0, 1, 0, -6, 0,
     0, 0, -4, 0, -1, 0, 0, 0, -6, 0, 0, 0, 1, 0, 2, 0, -2, 0, 8, 0,
     0, 0, 6, 0, 2, 0, 8, 0, 0, 0, 0, 0, 0, 0, -12, 0, -2, 0, 1, 0] := by
  eta_coeff

end WeightTwoCusps
