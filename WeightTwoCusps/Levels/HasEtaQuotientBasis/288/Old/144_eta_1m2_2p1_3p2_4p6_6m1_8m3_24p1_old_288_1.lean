module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«144».New.«144_eta_1m2_2p1_3p2_4p6_6m1_8m3_24p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 288

The eta expression is `η(z)^(-2) η(2z) η(3z)^2 η(4z)^6 η(6z)^(-1) η(8z)^(-3) η(24z)`; see
[the local level table](../../TABLE.md#level-288).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_144_eta_1m2_2p1_3p2_4p6_6m1_8m3_24p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^2 η(4z)^6 η(6z)^(-1) η(8z)^(-3) η(24z)` at level 288. -/
abbrev cuspForm_144_eta_1m2_2p1_3p2_4p6_6m1_8m3_24p1_old_288_1 : gamma0CuspForms 288 :=
  gamma0RescaleToLevel cuspForm_144_eta_1m2_2p1_3p2_4p6_6m1_8m3_24p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_144_eta_1m2_2p1_3p2_4p6_6m1_8m3_24p1_old_288_1_eq_eta :
    cuspForm_144_eta_1m2_2p1_3p2_4p6_6m1_8m3_24p1_old_288_1 =
      etaQuotientCuspForm 288 sparse![288; 0 => -2, 1 => 1, 2 => 2, 3 => 6, 5 => -1, 7 => -3, 23 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_144_eta_1m2_2p1_3p2_4p6_6m1_8m3_24p1_old_288_1_first_coeffs :
    first_coeffs 100 cuspForm_144_eta_1m2_2p1_3p2_4p6_6m1_8m3_24p1_old_288_1 =
    [0, 1, 2, 4, 6, 4, 4, 0, 0, 4, 2, 8, 0, -2, 0, -8, 0, -4, -4, 4,
     0, 0, -4, -16, 0, -1, -4, 4, -24, -12, -8, -8, 0, -16, -2, 0, 0, 6, -8, -8,
     0, 12, 0, -4, 0, -8, 8, 0, 0, -7, -2, 8, 12, 4, 4, 8, 0, 16, -6, 8,
     0, -2, 16, 0, 0, -8, 16, 4, 0, 32, 0, 16, 0, 10, 12, -4, 48, 0, -8, 8,
     0, 4, 6, -8, 0, -4, 8, 24, 0, 12, 8, 0, 0, -32, 0, 16, 0, 2, -14, -16] := by
  eta_coeff

end WeightTwoCusps
