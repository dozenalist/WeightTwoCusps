module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«144».New.«144_eta_1m3_2p6_3p1_4p1_6m2_8m2_12p1_24p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 432

The eta expression is `η(3z)^(-3) η(6z)^6 η(9z) η(12z) η(18z)^(-2) η(24z)^(-2) η(36z) η(72z)^2`; see
[the local level table](../../TABLE.md#level-432).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_144_eta_1m3_2p6_3p1_4p1_6m2_8m2_12p1_24p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-3) η(6z)^6 η(9z) η(12z) η(18z)^(-2) η(24z)^(-2) η(36z) η(72z)^2` at level 432. -/
abbrev cuspForm_144_eta_1m3_2p6_3p1_4p1_6m2_8m2_12p1_24p2_old_432_3 : gamma0CuspForms 432 :=
  gamma0Rescale cuspForm_144_eta_1m3_2p6_3p1_4p1_6m2_8m2_12p1_24p2 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_144_eta_1m3_2p6_3p1_4p1_6m2_8m2_12p1_24p2_old_432_3_eq_eta :
    cuspForm_144_eta_1m3_2p6_3p1_4p1_6m2_8m2_12p1_24p2_old_432_3 =
      etaQuotientCuspForm 432 sparse![432; 2 => -3, 5 => 6, 8 => 1, 11 => 1, 17 => -2, 23 => -2, 35 => 1, 71 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_144_eta_1m3_2p6_3p1_4p1_6m2_8m2_12p1_24p2_old_432_3_first_coeffs :
    first_coeffs 100 cuspForm_144_eta_1m3_2p6_3p1_4p1_6m2_8m2_12p1_24p2_old_432_3 =
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 3, 0, 0, 2, 0,
     0, -3, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 6, 0, 0, 0, 0, 0, -3,
     0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, -3, 0, 0, -2, 0, 0, 9, 0, 0,
     0, 0, 0, 0, 0, 0, -2, 0, 0, -12, 0, 0, 0, 0, 0, 3, 0, 0, -2, 0,
     0, 3, 0, 0, -12, 0, 0, -9, 0, 0, -4, 0, 0, -9, 0, 0, 0, 0, 0, -12] := by
  eta_coeff

end WeightTwoCusps
