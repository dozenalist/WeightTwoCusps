module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«204».New.«204_eta_1m3_2p8_3p1_4m3_6m2_12p1_17m3_34p8_51p1_68m3_102m2_204p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 408

The eta expression is `η(2z)^(-3) η(4z)^8 η(6z) η(8z)^(-3) η(12z)^(-2) η(24z) η(34z)^(-3) η(68z)^8 η(102z) η(136z)^(-3) η(204z)^(-2) η(408z)`; see
[the local level table](../../TABLE.md#level-408).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_204_eta_1m3_2p8_3p1_4m3_6m2_12p1_17m3_34p8_51p1_68m3_102m2_204p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-3) η(4z)^8 η(6z) η(8z)^(-3) η(12z)^(-2) η(24z) η(34z)^(-3) η(68z)^8 η(102z) η(136z)^(-3) η(204z)^(-2) η(408z)` at level 408. -/
abbrev cuspForm_204_eta_1m3_2p8_3p1_4m3_6m2_12p1_17m3_34p8_51p1_68m3_102m2_204p1_old_408_2 : gamma0CuspForms 408 :=
  gamma0Rescale cuspForm_204_eta_1m3_2p8_3p1_4m3_6m2_12p1_17m3_34p8_51p1_68m3_102m2_204p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_204_eta_1m3_2p8_3p1_4m3_6m2_12p1_17m3_34p8_51p1_68m3_102m2_204p1_old_408_2_eq_eta :
    cuspForm_204_eta_1m3_2p8_3p1_4m3_6m2_12p1_17m3_34p8_51p1_68m3_102m2_204p1_old_408_2 =
      etaQuotientCuspForm 408 sparse![408; 1 => -3, 3 => 8, 5 => 1, 7 => -3, 11 => -2, 23 => 1, 33 => -3, 67 => 8, 101 => 1, 135 => -3, 203 => -2, 407 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_204_eta_1m3_2p8_3p1_4m3_6m2_12p1_17m3_34p8_51p1_68m3_102m2_204p1_old_408_2_first_coeffs :
    first_coeffs 100 cuspForm_204_eta_1m3_2p8_3p1_4m3_6m2_12p1_17m3_34p8_51p1_68m3_102m2_204p1_old_408_2 =
    [0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 1, 0, -3, 0, -1, 0, 0, 0, -1, 0,
     0, 0, -2, 0, 0, 0, -1, 0, -3, 0, 1, 0, -3, 0, 0, 0, 3, 0, 1, 0,
     6, 0, 7, 0, 3, 0, -8, 0, -3, 0, 3, 0, 0, 0, 0, 0, -9, 0, 2, 0,
     0, 0, -9, 0, 0, 0, -8, 0, 0, 0, 8, 0, 6, 0, 10, 0, 0, 0, 1, 0,
     0, 0, -3, 0, 9, 0, 9, 0, -3, 0, -11, 0, 3, 0, 8, 0, -6, 0, -10, 0] := by
  eta_coeff

end WeightTwoCusps
