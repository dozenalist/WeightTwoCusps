module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«96».New.«96_eta_1m3_2p7_3p1_4m2_6m1_24p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 288

The eta expression is `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-2) η(6z)^(-1) η(24z)^2`; see
[the local level table](../../TABLE.md#level-288).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_96_eta_1m3_2p7_3p1_4m2_6m1_24p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-2) η(6z)^(-1) η(24z)^2` at level 288. -/
abbrev cuspForm_96_eta_1m3_2p7_3p1_4m2_6m1_24p2_old_288_1 : gamma0CuspForms 288 :=
  gamma0RescaleToLevel cuspForm_96_eta_1m3_2p7_3p1_4m2_6m1_24p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_96_eta_1m3_2p7_3p1_4m2_6m1_24p2_old_288_1_eq_eta :
    cuspForm_96_eta_1m3_2p7_3p1_4m2_6m1_24p2_old_288_1 =
      etaQuotientCuspForm 288 sparse![288; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -1, 23 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_96_eta_1m3_2p7_3p1_4m2_6m1_24p2_old_288_1_first_coeffs :
    first_coeffs 100 cuspForm_96_eta_1m3_2p7_3p1_4m2_6m1_24p2_old_288_1 =
    [0, 0, 1, 3, 2, 0, 1, 0, 0, 0, -2, 0, -2, 0, 0, -6, 0, 0, 1, 0,
     -4, 0, -4, 0, 0, 0, -2, -9, 0, 0, -2, 0, 0, 0, 2, 0, 2, 0, 4, 18,
     0, 0, 0, 0, 8, 0, 8, 0, 0, 0, -1, 6, -4, 0, 1, 0, 0, 0, 6, 0,
     4, 0, -8, 0, 0, 0, -4, 0, 4, 0, 0, 0, 0, 0, 6, -3, -8, 0, -2, 0,
     0, 0, -6, 0, 0, 0, -4, -30, 0, 0, -2, 0, -16, 0, 0, 0, 0, 0, -7, 0] := by
  eta_coeff

end WeightTwoCusps
