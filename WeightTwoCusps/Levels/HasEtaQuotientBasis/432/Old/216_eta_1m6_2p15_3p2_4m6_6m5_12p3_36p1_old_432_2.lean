module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«216».New.«216_eta_1m6_2p15_3p2_4m6_6m5_12p3_36p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 432

The eta expression is `η(2z)^(-6) η(4z)^15 η(6z)^2 η(8z)^(-6) η(12z)^(-5) η(24z)^3 η(72z)`; see
[the local level table](../../TABLE.md#level-432).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_216_eta_1m6_2p15_3p2_4m6_6m5_12p3_36p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-6) η(4z)^15 η(6z)^2 η(8z)^(-6) η(12z)^(-5) η(24z)^3 η(72z)` at level 432. -/
abbrev cuspForm_216_eta_1m6_2p15_3p2_4m6_6m5_12p3_36p1_old_432_2 : gamma0CuspForms 432 :=
  gamma0Rescale cuspForm_216_eta_1m6_2p15_3p2_4m6_6m5_12p3_36p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_216_eta_1m6_2p15_3p2_4m6_6m5_12p3_36p1_old_432_2_eq_eta :
    cuspForm_216_eta_1m6_2p15_3p2_4m6_6m5_12p3_36p1_old_432_2 =
      etaQuotientCuspForm 432 sparse![432; 1 => -6, 3 => 15, 5 => 2, 7 => -6, 11 => -5, 23 => 3, 71 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_216_eta_1m6_2p15_3p2_4m6_6m5_12p3_36p1_old_432_2_first_coeffs :
    first_coeffs 100 cuspForm_216_eta_1m6_2p15_3p2_4m6_6m5_12p3_36p1_old_432_2 =
    [0, 0, 0, 0, 1, 0, 6, 0, 12, 0, 6, 0, -6, 0, 0, 0, 12, 0, 12, 0,
     12, 0, 6, 0, 0, 0, 0, 0, -7, 0, 6, 0, 12, 0, -6, 0, 0, 0, 0, 0,
     0, 0, 0, 0, -12, 0, 6, 0, 0, 0, 0, 0, 17, 0, -12, 0, -12, 0, 0, 0,
     0, 0, 0, 0, -24, 0, -12, 0, 0, 0, -18, 0, 0, 0, 0, 0, -13, 0, -12, 0,
     -36, 0, 0, 0, 24, 0, 0, 0, 0, 0, -24, 0, -24, 0, -18, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
