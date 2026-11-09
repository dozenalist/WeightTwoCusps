module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«228».New.«228_eta_1m4_2p10_3p1_4m4_6m2_12p1_57p1_228p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(2z)^(-4) η(4z)^10 η(6z) η(8z)^(-4) η(12z)^(-2) η(24z) η(114z) η(456z)`; see
[the local level table](../../TABLE.md#level-456).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_228_eta_1m4_2p10_3p1_4m4_6m2_12p1_57p1_228p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-4) η(4z)^10 η(6z) η(8z)^(-4) η(12z)^(-2) η(24z) η(114z) η(456z)` at level 456. -/
abbrev cuspForm_228_eta_1m4_2p10_3p1_4m4_6m2_12p1_57p1_228p1_old_456_2 : gamma0CuspForms 456 :=
  gamma0Rescale cuspForm_228_eta_1m4_2p10_3p1_4m4_6m2_12p1_57p1_228p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_228_eta_1m4_2p10_3p1_4m4_6m2_12p1_57p1_228p1_old_456_2_eq_eta :
    cuspForm_228_eta_1m4_2p10_3p1_4m4_6m2_12p1_57p1_228p1_old_456_2 =
      etaQuotientCuspForm 456 sparse![456; 1 => -4, 3 => 10, 5 => 1, 7 => -4, 11 => -2, 23 => 1, 113 => 1, 455 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_228_eta_1m4_2p10_3p1_4m4_6m2_12p1_57p1_228p1_old_456_2_first_coeffs :
    first_coeffs 100 cuspForm_228_eta_1m4_2p10_3p1_4m4_6m2_12p1_57p1_228p1_old_456_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 4, 0, 4, 0, -1, 0, 0, 0, 4, 0, 1, 0, 0, 0,
     0, 0, 2, 0, 4, 0, -4, 0, -2, 0, 0, 0, -4, 0, 1, 0, 0, 0, 4, 0,
     0, 0, -8, 0, 0, 0, -1, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0,
     -4, 0, -4, 0, -2, 0, 0, 0, -4, 0, 0, 0, 0, 0, -4, 0, 3, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
