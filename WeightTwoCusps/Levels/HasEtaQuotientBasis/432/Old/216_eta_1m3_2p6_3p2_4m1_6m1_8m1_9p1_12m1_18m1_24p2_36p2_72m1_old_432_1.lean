module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«216».New.«216_eta_1m3_2p6_3p2_4m1_6m1_8m1_9p1_12m1_18m1_24p2_36p2_72m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 432

The eta expression is `η(z)^(-3) η(2z)^6 η(3z)^2 η(4z)^(-1) η(6z)^(-1) η(8z)^(-1) η(9z) η(12z)^(-1) η(18z)^(-1) η(24z)^2 η(36z)^2 η(72z)^(-1)`; see
[the local level table](../../TABLE.md#level-432).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_216_eta_1m3_2p6_3p2_4m1_6m1_8m1_9p1_12m1_18m1_24p2_36p2_72m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z)^2 η(4z)^(-1) η(6z)^(-1) η(8z)^(-1) η(9z) η(12z)^(-1) η(18z)^(-1) η(24z)^2 η(36z)^2 η(72z)^(-1)` at level 432. -/
abbrev cuspForm_216_eta_1m3_2p6_3p2_4m1_6m1_8m1_9p1_12m1_18m1_24p2_36p2_72m1_old_432_1 : gamma0CuspForms 432 :=
  gamma0RescaleToLevel cuspForm_216_eta_1m3_2p6_3p2_4m1_6m1_8m1_9p1_12m1_18m1_24p2_36p2_72m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_216_eta_1m3_2p6_3p2_4m1_6m1_8m1_9p1_12m1_18m1_24p2_36p2_72m1_old_432_1_eq_eta :
    cuspForm_216_eta_1m3_2p6_3p2_4m1_6m1_8m1_9p1_12m1_18m1_24p2_36p2_72m1_old_432_1 =
      etaQuotientCuspForm 432 sparse![432; 0 => -3, 1 => 6, 2 => 2, 3 => -1, 5 => -1, 7 => -1, 8 => 1, 11 => -1, 17 => -1, 23 => 2, 35 => 2, 71 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_216_eta_1m3_2p6_3p2_4m1_6m1_8m1_9p1_12m1_18m1_24p2_36p2_72m1_old_432_1_first_coeffs :
    first_coeffs 100 cuspForm_216_eta_1m3_2p6_3p2_4m1_6m1_8m1_9p1_12m1_18m1_24p2_36p2_72m1_old_432_1 =
    [0, 1, 3, 3, 2, 1, 0, 1, -1, 0, 0, -5, 0, -3, -3, 0, -4, 8, 0, -1,
     3, -12, 0, -2, 0, 3, -12, 0, -2, -6, 0, -4, -1, 0, 0, 3, 0, -5, 6, 6,
     0, 6, 0, 0, -3, 0, 0, -6, 0, 10, 12, 0, 10, -5, 0, 8, 1, 24, 0, 4,
     0, -9, 15, 0, 8, 4, 0, 11, 0, 0, 0, 8, 0, 9, 6, -15, -14, -15, 0, -9,
     3, 0, 0, 11, 0, -8, -30, 0, 0, -6, 0, -19, -6, -12, 0, 2, 0, 5, -18, 0] := by
  eta_coeff

end WeightTwoCusps
