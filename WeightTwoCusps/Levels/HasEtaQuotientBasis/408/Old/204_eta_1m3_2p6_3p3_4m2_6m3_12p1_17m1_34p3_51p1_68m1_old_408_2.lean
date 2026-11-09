module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«204».New.«204_eta_1m3_2p6_3p3_4m2_6m3_12p1_17m1_34p3_51p1_68m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 408

The eta expression is `η(2z)^(-3) η(4z)^6 η(6z)^3 η(8z)^(-2) η(12z)^(-3) η(24z) η(34z)^(-1) η(68z)^3 η(102z) η(136z)^(-1)`; see
[the local level table](../../TABLE.md#level-408).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_204_eta_1m3_2p6_3p3_4m2_6m3_12p1_17m1_34p3_51p1_68m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-3) η(4z)^6 η(6z)^3 η(8z)^(-2) η(12z)^(-3) η(24z) η(34z)^(-1) η(68z)^3 η(102z) η(136z)^(-1)` at level 408. -/
abbrev cuspForm_204_eta_1m3_2p6_3p3_4m2_6m3_12p1_17m1_34p3_51p1_68m1_old_408_2 : gamma0CuspForms 408 :=
  gamma0Rescale cuspForm_204_eta_1m3_2p6_3p3_4m2_6m3_12p1_17m1_34p3_51p1_68m1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_204_eta_1m3_2p6_3p3_4m2_6m3_12p1_17m1_34p3_51p1_68m1_old_408_2_eq_eta :
    cuspForm_204_eta_1m3_2p6_3p3_4m2_6m3_12p1_17m1_34p3_51p1_68m1_old_408_2 =
      etaQuotientCuspForm 408 sparse![408; 1 => -3, 3 => 6, 5 => 3, 7 => -2, 11 => -3, 23 => 1, 33 => -1, 67 => 3, 101 => 1, 135 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_204_eta_1m3_2p6_3p3_4m2_6m3_12p1_17m1_34p3_51p1_68m1_old_408_2_first_coeffs :
    first_coeffs 100 cuspForm_204_eta_1m3_2p6_3p3_4m2_6m3_12p1_17m1_34p3_51p1_68m1_old_408_2 =
    [0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 3, 0, 1, 0, -1, 0, 0, 0, 3, 0,
     2, 0, 2, 0, 0, 0, -3, 0, -1, 0, -1, 0, 3, 0, 0, 0, -3, 0, 1, 0,
     -2, 0, 3, 0, 3, 0, 0, 0, -1, 0, -3, 0, 4, 0, 2, 0, -1, 0, 0, 0,
     -2, 0, -3, 0, -4, 0, 0, 0, 0, 0, -4, 0, -2, 0, -4, 0, -4, 0, -3, 0,
     -2, 0, 1, 0, -3, 0, -3, 0, 1, 0, -5, 0, -3, 0, 4, 0, -4, 0, -2, 0] := by
  eta_coeff

end WeightTwoCusps
