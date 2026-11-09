module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«70».New.«70_eta_1p1_5p2_10m1_14p1_35m1_70p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(3z) η(15z)^2 η(30z)^(-1) η(42z) η(105z)^(-1) η(210z)^2`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_70_eta_1p1_5p2_10m1_14p1_35m1_70p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z) η(15z)^2 η(30z)^(-1) η(42z) η(105z)^(-1) η(210z)^2` at level 420. -/
abbrev cuspForm_70_eta_1p1_5p2_10m1_14p1_35m1_70p2_old_420_3 : gamma0CuspForms 420 :=
  gamma0RescaleToLevel cuspForm_70_eta_1p1_5p2_10m1_14p1_35m1_70p2 3 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_70_eta_1p1_5p2_10m1_14p1_35m1_70p2_old_420_3_eq_eta :
    cuspForm_70_eta_1p1_5p2_10m1_14p1_35m1_70p2_old_420_3 =
      etaQuotientCuspForm 420 sparse![420; 2 => 1, 14 => 2, 29 => -1, 41 => 1, 104 => -1, 209 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_70_eta_1p1_5p2_10m1_14p1_35m1_70p2_old_420_3_first_coeffs :
    first_coeffs 100 cuspForm_70_eta_1p1_5p2_10m1_14p1_35m1_70p2_old_420_3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0,
     0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 2, 0, 0, 3, 0, 0, 0,
     0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, -1, 0, 0,
     0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, -5, 0,
     0, -1, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 4, 0, 0, 0, 0, 0, -1] := by
  eta_coeff

end WeightTwoCusps
