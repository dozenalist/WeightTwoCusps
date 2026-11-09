module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«144».New.«144_eta_1m3_2p6_3p1_4p1_6m2_8m2_12p1_24p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 432

The eta expression is `η(z)^(-3) η(2z)^6 η(3z) η(4z) η(6z)^(-2) η(8z)^(-2) η(12z) η(24z)^2`; see
[the local level table](../../TABLE.md#level-432).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_144_eta_1m3_2p6_3p1_4p1_6m2_8m2_12p1_24p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z) η(4z) η(6z)^(-2) η(8z)^(-2) η(12z) η(24z)^2` at level 432. -/
abbrev cuspForm_144_eta_1m3_2p6_3p1_4p1_6m2_8m2_12p1_24p2_old_432_1 : gamma0CuspForms 432 :=
  gamma0RescaleToLevel cuspForm_144_eta_1m3_2p6_3p1_4p1_6m2_8m2_12p1_24p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_144_eta_1m3_2p6_3p1_4p1_6m2_8m2_12p1_24p2_old_432_1_eq_eta :
    cuspForm_144_eta_1m3_2p6_3p1_4p1_6m2_8m2_12p1_24p2_old_432_1 =
      etaQuotientCuspForm 432 sparse![432; 0 => -3, 1 => 6, 2 => 1, 3 => 1, 5 => -2, 7 => -2, 11 => 1, 23 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_144_eta_1m3_2p6_3p1_4p1_6m2_8m2_12p1_24p2_old_432_1_first_coeffs :
    first_coeffs 100 cuspForm_144_eta_1m3_2p6_3p1_4p1_6m2_8m2_12p1_24p2_old_432_1 =
    [0, 0, 1, 3, 3, 3, 2, -3, 0, 3, 1, 6, 0, -3, 0, -6, 0, -3, -2, 9,
     0, 0, -2, -12, 0, 3, -2, 3, -12, -9, -4, -9, 0, -12, -1, 0, 0, 12, -4, -6,
     0, 9, 0, 3, 0, -6, 4, 0, 0, -12, -1, 6, 6, 3, 2, 6, 0, 12, -3, 6,
     0, -12, 8, 0, 0, -6, 8, -9, 0, 24, 0, 12, 0, 15, 6, -3, 24, 0, -4, 3,
     0, 3, 3, -6, 0, -3, 4, 18, 0, 9, 4, -6, 0, -24, 0, 12, 0, -9, -7, -12] := by
  eta_coeff

end WeightTwoCusps
