module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«78».New.«78_eta_1p1_2p1_39p1_78p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 390

The eta expression is `η(5z) η(10z) η(195z) η(390z)`; see
[the local level table](../../TABLE.md#level-390).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(5z)` of `cuspForm_78_eta_1p1_2p1_39p1_78p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(5z) η(10z) η(195z) η(390z)` at level 390. -/
abbrev cuspForm_78_eta_1p1_2p1_39p1_78p1_old_390_5 : gamma0CuspForms 390 :=
  gamma0Rescale cuspForm_78_eta_1p1_2p1_39p1_78p1 5

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_78_eta_1p1_2p1_39p1_78p1_old_390_5_eq_eta :
    cuspForm_78_eta_1p1_2p1_39p1_78p1_old_390_5 =
      etaQuotientCuspForm 390 sparse![390; 4 => 1, 9 => 1, 194 => 1, 389 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_78_eta_1p1_2p1_39p1_78p1_old_390_5_first_coeffs :
    first_coeffs 100 cuspForm_78_eta_1p1_2p1_39p1_78p1_old_390_5 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -2, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 1, 0, 0, 0, 0,
     -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
