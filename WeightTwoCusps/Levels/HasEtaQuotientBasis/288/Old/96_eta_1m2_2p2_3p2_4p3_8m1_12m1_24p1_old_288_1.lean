module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«96».New.«96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 288

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^2 η(4z)^3 η(8z)^(-1) η(12z)^(-1) η(24z)`; see
[the local level table](../../TABLE.md#level-288).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^2 η(4z)^3 η(8z)^(-1) η(12z)^(-1) η(24z)` at level 288. -/
abbrev cuspForm_96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1_old_288_1 : gamma0CuspForms 288 :=
  gamma0RescaleToLevel cuspForm_96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1_old_288_1_eq_eta :
    cuspForm_96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1_old_288_1 =
      etaQuotientCuspForm 288 sparse![288; 0 => -2, 1 => 2, 2 => 2, 3 => 3, 7 => -1, 11 => -1, 23 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1_old_288_1_first_coeffs :
    first_coeffs 100 cuspForm_96_eta_1m2_2p2_3p2_4p3_8m1_12m1_24p1_old_288_1 =
    [0, 1, 2, 3, 4, 2, 2, 0, 0, 1, -4, 0, -4, -2, 0, -6, 0, -6, 2, 0,
     -8, -4, -8, 0, 0, -1, -4, -9, 0, 2, -4, 0, 0, 4, 4, 0, 4, -2, 8, 18,
     0, 2, 0, 0, 16, 2, 16, 0, 0, 9, -2, 6, -8, 10, 2, 0, 0, -4, 12, 0,
     8, 6, -16, 0, 0, -4, -8, 0, 8, 0, 0, 0, 0, -6, 12, -3, -16, -16, -4, 0,
     0, 1, -12, 0, 0, -12, -8, -30, 0, 10, -4, 0, -32, 4, 0, 0, 0, -14, -14, 0] := by
  eta_coeff

end WeightTwoCusps
