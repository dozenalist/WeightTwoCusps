module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«35».New.«35_eta_1p2_35p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(2z)^2 η(70z)^2`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_35_eta_1p2_35p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^2 η(70z)^2` at level 420. -/
abbrev cuspForm_35_eta_1p2_35p2_old_420_2 : gamma0CuspForms 420 :=
  gamma0RescaleToLevel cuspForm_35_eta_1p2_35p2 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_35_eta_1p2_35p2_old_420_2_eq_eta :
    cuspForm_35_eta_1p2_35p2_old_420_2 =
      etaQuotientCuspForm 420 sparse![420; 1 => 2, 69 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_35_eta_1p2_35p2_old_420_2_first_coeffs :
    first_coeffs 100 cuspForm_35_eta_1p2_35p2_old_420_2 =
    [0, 0, 0, 0, 0, 0, 1, 0, -2, 0, -1, 0, 2, 0, 1, 0, 2, 0, -2, 0,
     0, 0, -2, 0, -2, 0, 1, 0, 0, 0, 0, 0, 2, 0, 3, 0, -2, 0, 2, 0,
     0, 0, 0, 0, -2, 0, -2, 0, 0, 0, 0, 0, -2, 0, -1, 0, 0, 0, 2, 0,
     2, 0, -2, 0, 2, 0, 1, 0, 2, 0, 0, 0, 2, 0, -2, 0, -4, 0, 6, 0,
     2, 0, -6, 0, -2, 0, -8, 0, 4, 0, 0, 0, 4, 0, 5, 0, -4, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
