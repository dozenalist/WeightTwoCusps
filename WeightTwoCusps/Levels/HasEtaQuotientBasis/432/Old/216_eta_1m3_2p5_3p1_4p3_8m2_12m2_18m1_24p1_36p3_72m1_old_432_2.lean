module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«216».New.«216_eta_1m3_2p5_3p1_4p3_8m2_12m2_18m1_24p1_36p3_72m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 432

The eta expression is `η(2z)^(-3) η(4z)^5 η(6z) η(8z)^3 η(16z)^(-2) η(24z)^(-2) η(36z)^(-1) η(48z) η(72z)^3 η(144z)^(-1)`; see
[the local level table](../../TABLE.md#level-432).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_216_eta_1m3_2p5_3p1_4p3_8m2_12m2_18m1_24p1_36p3_72m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-3) η(4z)^5 η(6z) η(8z)^3 η(16z)^(-2) η(24z)^(-2) η(36z)^(-1) η(48z) η(72z)^3 η(144z)^(-1)` at level 432. -/
abbrev cuspForm_216_eta_1m3_2p5_3p1_4p3_8m2_12m2_18m1_24p1_36p3_72m1_old_432_2 : gamma0CuspForms 432 :=
  gamma0Rescale cuspForm_216_eta_1m3_2p5_3p1_4p3_8m2_12m2_18m1_24p1_36p3_72m1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_216_eta_1m3_2p5_3p1_4p3_8m2_12m2_18m1_24p1_36p3_72m1_old_432_2_eq_eta :
    cuspForm_216_eta_1m3_2p5_3p1_4p3_8m2_12m2_18m1_24p1_36p3_72m1_old_432_2 =
      etaQuotientCuspForm 432 sparse![432; 1 => -3, 3 => 5, 5 => 1, 7 => 3, 15 => -2, 23 => -2, 35 => -1, 47 => 1, 71 => 3, 143 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_216_eta_1m3_2p5_3p1_4p3_8m2_12m2_18m1_24p1_36p3_72m1_old_432_2_first_coeffs :
    first_coeffs 100 cuspForm_216_eta_1m3_2p5_3p1_4p3_8m2_12m2_18m1_24p1_36p3_72m1_old_432_2 =
    [0, 0, 1, 0, 3, 0, 4, 0, 6, 0, 5, 0, 0, 0, 1, 0, -3, 0, -4, 0,
     0, 0, -7, 0, 0, 0, -3, 0, -3, 0, 4, 0, -12, 0, 4, 0, 0, 0, -1, 0,
     9, 0, -12, 0, 0, 0, -10, 0, 0, 0, 3, 0, -12, 0, 4, 0, -6, 0, 6, 0,
     0, 0, -4, 0, -3, 0, -8, 0, 0, 0, -3, 0, 0, 0, -5, 0, 6, 0, 4, 0,
     0, 0, -6, 0, 0, 0, 0, 0, -9, 0, 8, 0, 0, 0, 6, 0, 0, 0, 10, 0] := by
  eta_coeff

end WeightTwoCusps
