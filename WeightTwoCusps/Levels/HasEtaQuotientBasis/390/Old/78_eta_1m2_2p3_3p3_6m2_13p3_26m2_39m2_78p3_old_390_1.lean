module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«78».New.«78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 390

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^3 η(6z)^(-2) η(13z)^3 η(26z)^(-2) η(39z)^(-2) η(78z)^3`; see
[the local level table](../../TABLE.md#level-390).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^3 η(6z)^(-2) η(13z)^3 η(26z)^(-2) η(39z)^(-2) η(78z)^3` at level 390. -/
abbrev cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3_old_390_1 : gamma0CuspForms 390 :=
  gamma0RescaleToLevel cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3_old_390_1_eq_eta :
    cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3_old_390_1 =
      etaQuotientCuspForm 390 sparse![390; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 12 => 3, 25 => -2, 38 => -2, 77 => 3] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3_old_390_1_first_coeffs :
    first_coeffs 100 cuspForm_78_eta_1m2_2p3_3p3_6m2_13p3_26m2_39m2_78p3_old_390_1 =
    [0, 0, 0, 0, 0, 0, 1, 2, 2, 1, -1, 0, 0, 1, 1, -3, -2, -3, 1, -2,
     -8, -5, -6, 2, -1, -1, -3, -6, 10, 6, 7, -2, 0, 12, 0, 11, 1, 0, 4, 2,
     11, -10, -1, 3, 0, -1, -6, 10, -6, -1, 4, -5, 1, -4, 4, -12, -15, 4, 6, -6,
     -11, -2, -6, 3, 4, -1, -8, -4, 13, 4, -10, -6, 3, -2, 3, 5, -10, -4, -1, 6,
     4, -2, 12, 8, 3, 14, 14, 0, 2, -2, -2, 3, 2, -2, -11, -14, 1, 0, -8, -2] := by
  eta_coeff

end WeightTwoCusps
