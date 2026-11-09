module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«216».New.«216_eta_1m6_2p13_3p5_4m5_6m6_9m1_12p3_18p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 432

The eta expression is `η(2z)^(-6) η(4z)^13 η(6z)^5 η(8z)^(-5) η(12z)^(-6) η(18z)^(-1) η(24z)^3 η(36z)`; see
[the local level table](../../TABLE.md#level-432).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_216_eta_1m6_2p13_3p5_4m5_6m6_9m1_12p3_18p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-6) η(4z)^13 η(6z)^5 η(8z)^(-5) η(12z)^(-6) η(18z)^(-1) η(24z)^3 η(36z)` at level 432. -/
abbrev cuspForm_216_eta_1m6_2p13_3p5_4m5_6m6_9m1_12p3_18p1_old_432_2 : gamma0CuspForms 432 :=
  gamma0Rescale cuspForm_216_eta_1m6_2p13_3p5_4m5_6m6_9m1_12p3_18p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_216_eta_1m6_2p13_3p5_4m5_6m6_9m1_12p3_18p1_old_432_2_eq_eta :
    cuspForm_216_eta_1m6_2p13_3p5_4m5_6m6_9m1_12p3_18p1_old_432_2 =
      etaQuotientCuspForm 432 sparse![432; 1 => -6, 3 => 13, 5 => 5, 7 => -5, 11 => -6, 17 => -1, 23 => 3, 35 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_216_eta_1m6_2p13_3p5_4m5_6m6_9m1_12p3_18p1_old_432_2_first_coeffs :
    first_coeffs 100 cuspForm_216_eta_1m6_2p13_3p5_4m5_6m6_9m1_12p3_18p1_old_432_2 =
    [0, 0, 1, 0, 6, 0, 14, 0, 15, 0, 4, 0, -6, 0, 3, 0, 24, 0, 28, 0,
     15, 0, 4, 0, 0, 0, 4, 0, 6, 0, 14, 0, 15, 0, -4, 0, 0, 0, 2, 0,
     0, 0, 0, 0, -15, 0, 4, 0, 0, 0, -4, 0, 6, 0, -28, 0, -15, 0, 0, 0,
     0, 0, -7, 0, -48, 0, -28, 0, 0, 0, -12, 0, 0, 0, -6, 0, -30, 0, -28, 0,
     -45, 0, 0, 0, 24, 0, -2, 0, 0, 0, -56, 0, -30, 0, -12, 0, 0, 0, 2, 0] := by
  eta_coeff

end WeightTwoCusps
