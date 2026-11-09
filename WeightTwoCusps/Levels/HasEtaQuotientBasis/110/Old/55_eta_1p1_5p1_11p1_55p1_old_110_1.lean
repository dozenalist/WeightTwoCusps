module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«55».New.«55_eta_1p1_5p1_11p1_55p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 110

The eta expression is `η(z) η(5z) η(11z) η(55z)`; see
[the local level table](../../TABLE.md#level-110).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_55_eta_1p1_5p1_11p1_55p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(5z) η(11z) η(55z)` at level 110. -/
abbrev cuspForm_55_eta_1p1_5p1_11p1_55p1_old_110_1 : gamma0CuspForms 110 :=
  gamma0RescaleToLevel cuspForm_55_eta_1p1_5p1_11p1_55p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_55_eta_1p1_5p1_11p1_55p1_old_110_1_eq_eta :
    cuspForm_55_eta_1p1_5p1_11p1_55p1_old_110_1 =
      etaQuotientCuspForm 110 sparse![110; 0 => 1, 4 => 1, 10 => 1, 54 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_55_eta_1p1_5p1_11p1_55p1_old_110_1_first_coeffs :
    first_coeffs 100 cuspForm_55_eta_1p1_5p1_11p1_55p1_old_110_1 =
    [0, 0, 0, 1, -1, -1, 0, 0, 0, 1, 2, 0, 0, -2, 0, 0, 1, 0, -2, 0,
     -1, -2, 0, 1, 2, 0, 2, 1, 2, 2, -2, -1, -2, 1, -2, 2, -3, 1, 0, -4,
     0, 2, 0, 0, -1, 1, 0, -2, 2, 0, 0, 2, 2, 0, 2, -1, 0, 0, 0, -3,
     2, 2, 2, -2, 1, -2, 0, -1, -2, 1, -4, -3, 0, -2, 2, 1, 0, 0, 0, 2,
     3, 0, -4, 0, 0, 2, 0, 4, 0, 1, -2, 4, 0, 1, 2, 0, -2, -1, 0, 1] := by
  eta_coeff

end WeightTwoCusps
