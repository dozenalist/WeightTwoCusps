module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«84».New.«84_eta_1m3_2p8_4m3_7m1_14p2_21p2_28m1_42m2_84p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-3) η(2z)^8 η(4z)^(-3) η(7z)^(-1) η(14z)^2 η(21z)^2 η(28z)^(-1) η(42z)^(-2) η(84z)^2`; see
[the local level table](../../TABLE.md#level-252).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_84_eta_1m3_2p8_4m3_7m1_14p2_21p2_28m1_42m2_84p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^8 η(4z)^(-3) η(7z)^(-1) η(14z)^2 η(21z)^2 η(28z)^(-1) η(42z)^(-2) η(84z)^2` at level 252. -/
abbrev cuspForm_84_eta_1m3_2p8_4m3_7m1_14p2_21p2_28m1_42m2_84p2_old_252_1 : gamma0CuspForms 252 :=
  gamma0RescaleToLevel cuspForm_84_eta_1m3_2p8_4m3_7m1_14p2_21p2_28m1_42m2_84p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_84_eta_1m3_2p8_4m3_7m1_14p2_21p2_28m1_42m2_84p2_old_252_1_eq_eta :
    cuspForm_84_eta_1m3_2p8_4m3_7m1_14p2_21p2_28m1_42m2_84p2_old_252_1 =
      etaQuotientCuspForm 252 sparse![252; 0 => -3, 1 => 8, 3 => -3, 6 => -1, 13 => 2, 20 => 2, 27 => -1, 41 => -2, 83 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_84_eta_1m3_2p8_4m3_7m1_14p2_21p2_28m1_42m2_84p2_old_252_1_first_coeffs :
    first_coeffs 100 cuspForm_84_eta_1m3_2p8_4m3_7m1_14p2_21p2_28m1_42m2_84p2_old_252_1 =
    [0, 0, 0, 0, 0, 1, 3, 1, -2, 2, 1, -4, 0, 1, 1, 0, -2, 0, -6, -3,
     -1, 0, 4, -6, 1, -2, -7, -1, -1, 6, -2, 6, 4, -6, 0, -1, 6, 2, 5, 6,
     5, 8, 1, -2, 8, 1, -6, 10, -2, 0, -2, -2, -5, -8, 6, 0, 3, -6, -2, -3,
     -4, -9, -2, 3, -4, 2, -2, 4, -12, -2, -1, 2, -8, -8, 10, 0, 7, -4, -4, 0,
     3, -2, 8, -3, -4, -2, 6, 8, -4, 14, 1, 3, -6, 8, -6, 0, 7, -6, 0, -4] := by
  eta_coeff

end WeightTwoCusps
