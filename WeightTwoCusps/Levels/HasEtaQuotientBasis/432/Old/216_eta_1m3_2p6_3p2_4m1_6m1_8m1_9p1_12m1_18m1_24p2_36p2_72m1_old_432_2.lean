module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«216».New.«216_eta_1m3_2p6_3p2_4m1_6m1_8m1_9p1_12m1_18m1_24p2_36p2_72m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 432

The eta expression is `η(2z)^(-3) η(4z)^6 η(6z)^2 η(8z)^(-1) η(12z)^(-1) η(16z)^(-1) η(18z) η(24z)^(-1) η(36z)^(-1) η(48z)^2 η(72z)^2 η(144z)^(-1)`; see
[the local level table](../../TABLE.md#level-432).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_216_eta_1m3_2p6_3p2_4m1_6m1_8m1_9p1_12m1_18m1_24p2_36p2_72m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-3) η(4z)^6 η(6z)^2 η(8z)^(-1) η(12z)^(-1) η(16z)^(-1) η(18z) η(24z)^(-1) η(36z)^(-1) η(48z)^2 η(72z)^2 η(144z)^(-1)` at level 432. -/
abbrev cuspForm_216_eta_1m3_2p6_3p2_4m1_6m1_8m1_9p1_12m1_18m1_24p2_36p2_72m1_old_432_2 : gamma0CuspForms 432 :=
  gamma0Rescale cuspForm_216_eta_1m3_2p6_3p2_4m1_6m1_8m1_9p1_12m1_18m1_24p2_36p2_72m1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_216_eta_1m3_2p6_3p2_4m1_6m1_8m1_9p1_12m1_18m1_24p2_36p2_72m1_old_432_2_eq_eta :
    cuspForm_216_eta_1m3_2p6_3p2_4m1_6m1_8m1_9p1_12m1_18m1_24p2_36p2_72m1_old_432_2 =
      etaQuotientCuspForm 432 sparse![432; 1 => -3, 3 => 6, 5 => 2, 7 => -1, 11 => -1, 15 => -1, 17 => 1, 23 => -1, 35 => -1, 47 => 2, 71 => 2, 143 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_216_eta_1m3_2p6_3p2_4m1_6m1_8m1_9p1_12m1_18m1_24p2_36p2_72m1_old_432_2_first_coeffs :
    first_coeffs 100 cuspForm_216_eta_1m3_2p6_3p2_4m1_6m1_8m1_9p1_12m1_18m1_24p2_36p2_72m1_old_432_2 =
    [0, 0, 1, 0, 3, 0, 3, 0, 2, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0,
     0, 0, -5, 0, 0, 0, -3, 0, -3, 0, 0, 0, -4, 0, 8, 0, 0, 0, -1, 0,
     3, 0, -12, 0, 0, 0, -2, 0, 0, 0, 3, 0, -12, 0, 0, 0, -2, 0, -6, 0,
     0, 0, -4, 0, -1, 0, 0, 0, 0, 0, 3, 0, 0, 0, -5, 0, 6, 0, 6, 0,
     0, 0, 6, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, -6, 0, 0, 0, 10, 0] := by
  eta_coeff

end WeightTwoCusps
