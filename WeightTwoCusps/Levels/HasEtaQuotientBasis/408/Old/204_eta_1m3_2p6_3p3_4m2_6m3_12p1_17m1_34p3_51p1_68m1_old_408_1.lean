module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«204».New.«204_eta_1m3_2p6_3p3_4m2_6m3_12p1_17m1_34p3_51p1_68m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 408

The eta expression is `η(z)^(-3) η(2z)^6 η(3z)^3 η(4z)^(-2) η(6z)^(-3) η(12z) η(17z)^(-1) η(34z)^3 η(51z) η(68z)^(-1)`; see
[the local level table](../../TABLE.md#level-408).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_204_eta_1m3_2p6_3p3_4m2_6m3_12p1_17m1_34p3_51p1_68m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z)^3 η(4z)^(-2) η(6z)^(-3) η(12z) η(17z)^(-1) η(34z)^3 η(51z) η(68z)^(-1)` at level 408. -/
abbrev cuspForm_204_eta_1m3_2p6_3p3_4m2_6m3_12p1_17m1_34p3_51p1_68m1_old_408_1 : gamma0CuspForms 408 :=
  gamma0RescaleToLevel cuspForm_204_eta_1m3_2p6_3p3_4m2_6m3_12p1_17m1_34p3_51p1_68m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_204_eta_1m3_2p6_3p3_4m2_6m3_12p1_17m1_34p3_51p1_68m1_old_408_1_eq_eta :
    cuspForm_204_eta_1m3_2p6_3p3_4m2_6m3_12p1_17m1_34p3_51p1_68m1_old_408_1 =
      etaQuotientCuspForm 408 sparse![408; 0 => -3, 1 => 6, 2 => 3, 3 => -2, 5 => -3, 11 => 1, 16 => -1, 33 => 3, 50 => 1, 67 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_204_eta_1m3_2p6_3p3_4m2_6m3_12p1_17m1_34p3_51p1_68m1_old_408_1_first_coeffs :
    first_coeffs 100 cuspForm_204_eta_1m3_2p6_3p3_4m2_6m3_12p1_17m1_34p3_51p1_68m1_old_408_1 =
    [0, 0, 0, 1, 3, 3, 1, -1, 0, 3, 2, 2, 0, -3, -1, -1, 3, 0, -3, 1,
     -2, 3, 3, 0, -1, -3, 4, 2, -1, 0, -2, -3, -4, 0, 0, -4, -2, -4, -4, -3,
     -2, 1, -3, -3, 1, -5, -3, 4, -4, -2, -8, 1, 2, -10, 4, -3, -3, -3, 2, 4,
     -2, 4, 1, -3, -1, 3, 3, -2, 1, 4, -4, 3, -1, 0, 0, 0, 4, 0, -2, 3,
     6, 2, 8, 0, 5, -1, 6, 8, -3, 0, 2, 8, -3, 5, -2, -3, 11, 6, 6, 2] := by
  eta_coeff

end WeightTwoCusps
