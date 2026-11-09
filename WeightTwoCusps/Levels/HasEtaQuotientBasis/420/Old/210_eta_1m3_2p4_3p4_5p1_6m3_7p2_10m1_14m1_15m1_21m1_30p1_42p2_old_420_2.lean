module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«210».New.«210_eta_1m3_2p4_3p4_5p1_6m3_7p2_10m1_14m1_15m1_21m1_30p1_42p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(2z)^(-3) η(4z)^4 η(6z)^4 η(10z) η(12z)^(-3) η(14z)^2 η(20z)^(-1) η(28z)^(-1) η(30z)^(-1) η(42z)^(-1) η(60z) η(84z)^2`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_210_eta_1m3_2p4_3p4_5p1_6m3_7p2_10m1_14m1_15m1_21m1_30p1_42p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-3) η(4z)^4 η(6z)^4 η(10z) η(12z)^(-3) η(14z)^2 η(20z)^(-1) η(28z)^(-1) η(30z)^(-1) η(42z)^(-1) η(60z) η(84z)^2` at level 420. -/
abbrev cuspForm_210_eta_1m3_2p4_3p4_5p1_6m3_7p2_10m1_14m1_15m1_21m1_30p1_42p2_old_420_2 : gamma0CuspForms 420 :=
  gamma0Rescale cuspForm_210_eta_1m3_2p4_3p4_5p1_6m3_7p2_10m1_14m1_15m1_21m1_30p1_42p2 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_210_eta_1m3_2p4_3p4_5p1_6m3_7p2_10m1_14m1_15m1_21m1_30p1_42p2_old_420_2_eq_eta :
    cuspForm_210_eta_1m3_2p4_3p4_5p1_6m3_7p2_10m1_14m1_15m1_21m1_30p1_42p2_old_420_2 =
      etaQuotientCuspForm 420 sparse![420; 1 => -3, 3 => 4, 5 => 4, 9 => 1, 11 => -3, 13 => 2, 19 => -1, 27 => -1, 29 => -1, 41 => -1, 59 => 1, 83 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m3_2p4_3p4_5p1_6m3_7p2_10m1_14m1_15m1_21m1_30p1_42p2_old_420_2_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m3_2p4_3p4_5p1_6m3_7p2_10m1_14m1_15m1_21m1_30p1_42p2_old_420_2 =
    [0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 5, 0, 6, 0, 5, 0, 5, 0, 5, 0,
     5, 0, 4, 0, -1, 0, -4, 0, -5, 0, -2, 0, 2, 0, 1, 0, 0, 0, -1, 0,
     -1, 0, 4, 0, 4, 0, 1, 0, -4, 0, -10, 0, -4, 0, 1, 0, 7, 0, 5, 0,
     -2, 0, -5, 0, -4, 0, 0, 0, 1, 0, -5, 0, -17, 0, -17, 0, -11, 0, 2, 0,
     5, 0, 4, 0, -6, 0, -10, 0, -4, 0, 5, 0, 1, 0, -10, 0, -17, 0, -20, 0] := by
  eta_coeff

end WeightTwoCusps
