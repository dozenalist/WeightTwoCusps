module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«135».New.«135_eta_9p3_15p1_27m1_45m1_135p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 405

The eta expression is `η(9z)^3 η(15z) η(27z)^(-1) η(45z)^(-1) η(135z)^2`; see
[the local level table](../../TABLE.md#level-405).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_135_eta_9p3_15p1_27m1_45m1_135p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(9z)^3 η(15z) η(27z)^(-1) η(45z)^(-1) η(135z)^2` at level 405. -/
abbrev cuspForm_135_eta_9p3_15p1_27m1_45m1_135p2_old_405_1 : gamma0CuspForms 405 :=
  gamma0RescaleToLevel cuspForm_135_eta_9p3_15p1_27m1_45m1_135p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_135_eta_9p3_15p1_27m1_45m1_135p2_old_405_1_eq_eta :
    cuspForm_135_eta_9p3_15p1_27m1_45m1_135p2_old_405_1 =
      etaQuotientCuspForm 405 sparse![405; 8 => 3, 14 => 1, 26 => -1, 44 => -1, 134 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_135_eta_9p3_15p1_27m1_45m1_135p2_old_405_1_first_coeffs :
    first_coeffs 100 cuspForm_135_eta_9p3_15p1_27m1_45m1_135p2_old_405_1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -3,
     0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 6, 0, 0,
     -1, 0, 0, 0, 0, 0, -3, 0, 0, 3, 0, 0, -6, 0, 0, 1, 0, 0, 0, 0,
     0, 3, 0, 0, -3, 0, 0, -6, 0, 0, -1, 0, 0, -6, 0, 0, 3, 0, 0, 3,
     0, 0, 6, 0, 0, 0, 0, 0, 6, 0, 0, 3, 0, 0, 0, 0, 0, -6, 0, 0] := by
  eta_coeff

end WeightTwoCusps
