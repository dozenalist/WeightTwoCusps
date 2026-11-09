module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«55».New.«55_eta_1p1_5p1_11p1_55p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 220

The eta expression is `η(2z) η(10z) η(22z) η(110z)`; see
[the local level table](../../TABLE.md#level-220).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_55_eta_1p1_5p1_11p1_55p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(10z) η(22z) η(110z)` at level 220. -/
abbrev cuspForm_55_eta_1p1_5p1_11p1_55p1_old_220_2 : gamma0CuspForms 220 :=
  gamma0RescaleToLevel cuspForm_55_eta_1p1_5p1_11p1_55p1 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_55_eta_1p1_5p1_11p1_55p1_old_220_2_eq_eta :
    cuspForm_55_eta_1p1_5p1_11p1_55p1_old_220_2 =
      etaQuotientCuspForm 220 sparse![220; 1 => 1, 9 => 1, 21 => 1, 109 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_55_eta_1p1_5p1_11p1_55p1_old_220_2_first_coeffs :
    first_coeffs 100 cuspForm_55_eta_1p1_5p1_11p1_55p1_old_220_2 =
    [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0,
     2, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 1, 0, 0, 0, -2, 0, 0, 0,
     -1, 0, -2, 0, 0, 0, 1, 0, 2, 0, 0, 0, 2, 0, 1, 0, 2, 0, 2, 0,
     -2, 0, -1, 0, -2, 0, 1, 0, -2, 0, 2, 0, -3, 0, 1, 0, 0, 0, -4, 0,
     0, 0, 2, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, -2, 0, 2, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
