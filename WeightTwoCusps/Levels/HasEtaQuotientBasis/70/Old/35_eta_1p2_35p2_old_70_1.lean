module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«35».New.«35_eta_1p2_35p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 70

The eta expression is `η(z)^2 η(35z)^2`; see
[the local level table](../../TABLE.md#level-70).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_35_eta_1p2_35p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^2 η(35z)^2` at level 70. -/
abbrev cuspForm_35_eta_1p2_35p2_old_70_1 : gamma0CuspForms 70 :=
  gamma0RescaleToLevel cuspForm_35_eta_1p2_35p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_35_eta_1p2_35p2_old_70_1_eq_eta :
    cuspForm_35_eta_1p2_35p2_old_70_1 =
      etaQuotientCuspForm 70 sparse![70; 0 => 2, 34 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_35_eta_1p2_35p2_old_70_1_first_coeffs :
    first_coeffs 100 cuspForm_35_eta_1p2_35p2_old_70_1 =
    [0, 0, 0, 1, -2, -1, 2, 1, 2, -2, 0, -2, -2, 1, 0, 0, 2, 3, -2, 2,
     0, 0, -2, -2, 0, 0, -2, -1, 0, 2, 2, -2, 2, 1, 2, 0, 2, -2, -4, 6,
     2, -6, -2, -8, 4, 0, 4, 5, -4, 0, 0, -2, -6, 6, -2, 1, -2, 4, 6, 2,
     0, 4, 0, 0, -6, -4, 2, -2, -2, -8, 0, -4, 2, 2, 0, 1, 4, -1, 6, 2,
     -2, 4, 4, 4, 0, 0, -4, -5, 0, -8, -2, 4, 4, -2, -6, 0, 0, 3, 0, 0] := by
  eta_coeff

end WeightTwoCusps
