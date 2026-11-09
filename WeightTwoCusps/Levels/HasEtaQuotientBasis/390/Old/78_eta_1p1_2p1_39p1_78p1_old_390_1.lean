module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«78».New.«78_eta_1p1_2p1_39p1_78p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 390

The eta expression is `η(z) η(2z) η(39z) η(78z)`; see
[the local level table](../../TABLE.md#level-390).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_78_eta_1p1_2p1_39p1_78p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(2z) η(39z) η(78z)` at level 390. -/
abbrev cuspForm_78_eta_1p1_2p1_39p1_78p1_old_390_1 : gamma0CuspForms 390 :=
  gamma0RescaleToLevel cuspForm_78_eta_1p1_2p1_39p1_78p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_78_eta_1p1_2p1_39p1_78p1_old_390_1_eq_eta :
    cuspForm_78_eta_1p1_2p1_39p1_78p1_old_390_1 =
      etaQuotientCuspForm 390 sparse![390; 0 => 1, 1 => 1, 38 => 1, 77 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_78_eta_1p1_2p1_39p1_78p1_old_390_1_first_coeffs :
    first_coeffs 100 cuspForm_78_eta_1p1_2p1_39p1_78p1_old_390_1 =
    [0, 0, 0, 0, 0, 1, -1, -2, 1, 0, 2, 1, 0, 0, -2, 1, -2, -2, 0, 2,
     -1, 0, 2, 0, 2, 0, 1, 0, 0, -2, 0, 0, 0, -1, -2, -2, 0, 2, 0, 0,
     -2, 3, 0, 0, 1, 1, 2, 1, 0, 0, -2, -2, 0, 2, -1, 0, 4, 0, -4, -1,
     -1, -4, 2, -2, 0, -1, 0, 0, 2, 0, 2, 1, 1, 2, 2, 0, 0, 2, 0, 4,
     -5, 0, -2, -3, 2, 2, -4, 2, -6, -3, 2, 0, 0, -2, 6, 2, -1, -2, 4, 1] := by
  eta_coeff

end WeightTwoCusps
