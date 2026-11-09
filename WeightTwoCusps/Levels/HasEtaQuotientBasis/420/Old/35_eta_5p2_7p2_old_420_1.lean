module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«35».New.«35_eta_5p2_7p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(5z)^2 η(7z)^2`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_35_eta_5p2_7p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(5z)^2 η(7z)^2` at level 420. -/
abbrev cuspForm_35_eta_5p2_7p2_old_420_1 : gamma0CuspForms 420 :=
  gamma0RescaleToLevel cuspForm_35_eta_5p2_7p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_35_eta_5p2_7p2_old_420_1_eq_eta :
    cuspForm_35_eta_5p2_7p2_old_420_1 =
      etaQuotientCuspForm 420 sparse![420; 4 => 2, 6 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_35_eta_5p2_7p2_old_420_1_first_coeffs :
    first_coeffs 100 cuspForm_35_eta_5p2_7p2_old_420_1 =
    [0, 1, 0, 0, 0, 0, -2, 0, -2, 0, 0, -1, 0, 4, 0, -1, 2, 0, 2, 0,
     2, 1, 2, -4, 0, 1, 2, -4, -2, 1, -2, -2, -2, -4, -2, -1, 2, 4, 4, -1,
     -2, -6, 2, -2, 2, 2, -4, 4, 8, 1, 0, 5, -4, 6, 2, 2, 2, -2, -6, -2,
     2, 4, 0, -2, -2, -1, -2, -2, -4, 2, 0, 4, -2, 0, 0, 0, -8, -2, -6, -3,
     -2, -3, -4, 8, -2, -3, 4, 8, 0, -4, 2, 1, 8, -2, 6, -2, 0, -4, 0, 6] := by
  eta_coeff

end WeightTwoCusps
