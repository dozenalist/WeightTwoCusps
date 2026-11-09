module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«135».New.«135_eta_1m1_3p3_5p2_15m1_45p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 405

The eta expression is `η(z)^(-1) η(3z)^3 η(5z)^2 η(15z)^(-1) η(45z)`; see
[the local level table](../../TABLE.md#level-405).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_135_eta_1m1_3p3_5p2_15m1_45p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^3 η(5z)^2 η(15z)^(-1) η(45z)` at level 405. -/
abbrev cuspForm_135_eta_1m1_3p3_5p2_15m1_45p1_old_405_1 : gamma0CuspForms 405 :=
  gamma0RescaleToLevel cuspForm_135_eta_1m1_3p3_5p2_15m1_45p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_135_eta_1m1_3p3_5p2_15m1_45p1_old_405_1_eq_eta :
    cuspForm_135_eta_1m1_3p3_5p2_15m1_45p1_old_405_1 =
      etaQuotientCuspForm 405 sparse![405; 0 => -1, 2 => 3, 4 => 2, 14 => -1, 44 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_135_eta_1m1_3p3_5p2_15m1_45p1_old_405_1_first_coeffs :
    first_coeffs 100 cuspForm_135_eta_1m1_3p3_5p2_15m1_45p1_old_405_1 =
    [0, 0, 1, 1, 2, 0, 2, -1, 0, -4, 1, -2, -1, -5, 0, -2, -4, -2, 4, 4,
     -1, 0, 2, 0, -6, 3, 4, 4, -4, 2, -1, 2, -1, 8, 8, 2, 4, -3, 1, -2,
     0, 2, 0, -2, -4, -4, -6, 4, -1, 4, 1, -4, 0, -2, -4, 1, -6, 4, -2, -2,
     2, 4, -3, 0, 0, -2, 4, -7, -1, 0, -3, 2, -12, 1, 2, 1, -6, 0, -4, -10,
     -1, -4, 10, 0, 0, 4, -2, 4, 0, 6, 4, 10, 3, 0, -4, -2, 10, 3, 5, 16] := by
  eta_coeff

end WeightTwoCusps
