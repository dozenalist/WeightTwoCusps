module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«126».New.«126_eta_1m2_2p1_3p7_6m3_7m2_9m2_14p4_18p1_21p1_42m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-2) η(2z) η(3z)^7 η(6z)^(-3) η(7z)^(-2) η(9z)^(-2) η(14z)^4 η(18z) η(21z) η(42z)^(-1)`; see
[the local level table](../../TABLE.md#level-252).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_126_eta_1m2_2p1_3p7_6m3_7m2_9m2_14p4_18p1_21p1_42m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^7 η(6z)^(-3) η(7z)^(-2) η(9z)^(-2) η(14z)^4 η(18z) η(21z) η(42z)^(-1)` at level 252. -/
abbrev cuspForm_126_eta_1m2_2p1_3p7_6m3_7m2_9m2_14p4_18p1_21p1_42m1_old_252_1 : gamma0CuspForms 252 :=
  gamma0RescaleToLevel cuspForm_126_eta_1m2_2p1_3p7_6m3_7m2_9m2_14p4_18p1_21p1_42m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_126_eta_1m2_2p1_3p7_6m3_7m2_9m2_14p4_18p1_21p1_42m1_old_252_1_eq_eta :
    cuspForm_126_eta_1m2_2p1_3p7_6m3_7m2_9m2_14p4_18p1_21p1_42m1_old_252_1 =
      etaQuotientCuspForm 252 sparse![252; 0 => -2, 1 => 1, 2 => 7, 5 => -3, 6 => -2, 8 => -2, 13 => 4, 17 => 1, 20 => 1, 41 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_126_eta_1m2_2p1_3p7_6m3_7m2_9m2_14p4_18p1_21p1_42m1_old_252_1_first_coeffs :
    first_coeffs 100 cuspForm_126_eta_1m2_2p1_3p7_6m3_7m2_9m2_14p4_18p1_21p1_42m1_old_252_1 =
    [0, 1, 2, 4, 1, 0, -4, 1, 2, 4, 6, 0, 4, -10, 2, -3, 1, 0, -7, 8,
     -12, 1, -6, 0, 2, -11, 4, -14, 1, 0, 3, -4, -10, 0, -6, 0, 4, 8, -8, -7,
     -6, 0, -1, 14, 12, 0, 0, 0, -2, 1, 14, 12, -10, 0, 14, 0, 2, 5, 12, 0,
     -3, 14, -8, 4, 7, 0, -12, -4, 12, 6, 0, 0, -1, -10, 4, -14, 8, 0, 19, 2,
     12, 19, -18, 0, 1, 12, -8, -18, 12, 0, 6, -4, -12, -10, 12, 0, -4, -10, 2, 6] := by
  eta_coeff

end WeightTwoCusps
