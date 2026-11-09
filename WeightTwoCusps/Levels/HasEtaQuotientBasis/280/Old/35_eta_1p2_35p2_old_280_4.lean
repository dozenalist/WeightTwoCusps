module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«35».New.«35_eta_1p2_35p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 280

The eta expression is `η(4z)^2 η(140z)^2`; see
[the local level table](../../TABLE.md#level-280).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_35_eta_1p2_35p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^2 η(140z)^2` at level 280. -/
abbrev cuspForm_35_eta_1p2_35p2_old_280_4 : gamma0CuspForms 280 :=
  gamma0RescaleToLevel cuspForm_35_eta_1p2_35p2 4 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_35_eta_1p2_35p2_old_280_4_eq_eta :
    cuspForm_35_eta_1p2_35p2_old_280_4 =
      etaQuotientCuspForm 280 sparse![280; 3 => 2, 139 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_35_eta_1p2_35p2_old_280_4_first_coeffs :
    first_coeffs 100 cuspForm_35_eta_1p2_35p2_old_280_4 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -2, 0, 0, 0,
     -1, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, -2, 0, 0, 0,
     0, 0, 0, 0, -2, 0, 0, 0, -2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, -2, 0, 0, 0, 2, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
