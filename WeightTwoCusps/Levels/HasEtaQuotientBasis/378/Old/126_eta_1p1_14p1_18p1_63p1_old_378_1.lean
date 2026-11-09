module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«126».New.«126_eta_1p1_14p1_18p1_63p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 378

The eta expression is `η(z) η(14z) η(18z) η(63z)`; see
[the local level table](../../TABLE.md#level-378).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_126_eta_1p1_14p1_18p1_63p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(14z) η(18z) η(63z)` at level 378. -/
abbrev cuspForm_126_eta_1p1_14p1_18p1_63p1_old_378_1 : gamma0CuspForms 378 :=
  gamma0RescaleToLevel cuspForm_126_eta_1p1_14p1_18p1_63p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_126_eta_1p1_14p1_18p1_63p1_old_378_1_eq_eta :
    cuspForm_126_eta_1p1_14p1_18p1_63p1_old_378_1 =
      etaQuotientCuspForm 378 sparse![378; 0 => 1, 13 => 1, 17 => 1, 62 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_126_eta_1p1_14p1_18p1_63p1_old_378_1_first_coeffs :
    first_coeffs 100 cuspForm_126_eta_1p1_14p1_18p1_63p1_old_378_1 =
    [0, 0, 0, 0, 1, -1, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, -1, 0, -1, 0,
     1, 0, -1, 0, 1, -1, 1, -1, 0, -1, 2, 0, -1, 2, 2, 0, 1, -1, -1, -2,
     -2, 2, 1, 1, -2, -1, 0, 0, -2, 0, 1, -2, 0, 1, 0, 2, -1, 2, 1, 1,
     0, 2, 0, 0, 0, -1, -2, 0, 2, -2, -1, -1, 1, 0, -1, 0, 0, 0, 0, 1,
     1, 1, 0, -3, 0, 0, -1, 0, 2, -4, 1, -1, 1, 0, 2, 1, -1, -4, 0, 0] := by
  eta_coeff

end WeightTwoCusps
