module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«144».New.«144_eta_1m1_2m1_3p1_4p6_8m1_16m1_48p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 288

The eta expression is `η(z)^(-1) η(2z)^(-1) η(3z) η(4z)^6 η(8z)^(-1) η(16z)^(-1) η(48z)`; see
[the local level table](../../TABLE.md#level-288).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_144_eta_1m1_2m1_3p1_4p6_8m1_16m1_48p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^(-1) η(3z) η(4z)^6 η(8z)^(-1) η(16z)^(-1) η(48z)` at level 288. -/
abbrev cuspForm_144_eta_1m1_2m1_3p1_4p6_8m1_16m1_48p1_old_288_1 : gamma0CuspForms 288 :=
  gamma0RescaleToLevel cuspForm_144_eta_1m1_2m1_3p1_4p6_8m1_16m1_48p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_144_eta_1m1_2m1_3p1_4p6_8m1_16m1_48p1_old_288_1_eq_eta :
    cuspForm_144_eta_1m1_2m1_3p1_4p6_8m1_16m1_48p1_old_288_1 =
      etaQuotientCuspForm 288 sparse![288; 0 => -1, 1 => -1, 2 => 1, 3 => 6, 7 => -1, 15 => -1, 47 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_144_eta_1m1_2m1_3p1_4p6_8m1_16m1_48p1_old_288_1_first_coeffs :
    first_coeffs 100 cuspForm_144_eta_1m1_2m1_3p1_4p6_8m1_16m1_48p1_old_288_1 =
    [0, 0, 1, 1, 3, 3, 2, 3, 0, 3, 1, 2, 0, -3, 0, -2, 0, -3, -2, -5,
     0, 0, -2, -4, 0, 3, -2, 1, -12, -9, -4, 1, 0, -12, -1, 0, 0, 12, -4, -2,
     0, 9, 0, -7, 0, -6, 4, 0, 0, -12, -1, 2, 6, 3, 2, 2, 0, 12, -3, 2,
     0, -12, 8, 0, 0, -6, 8, 13, 0, 24, 0, 4, 0, 15, 6, -1, 24, 0, -4, 5,
     0, 3, 3, -2, 0, -3, 4, 6, 0, 9, 4, 6, 0, -24, 0, 4, 0, -9, -7, -4] := by
  eta_coeff

end WeightTwoCusps
