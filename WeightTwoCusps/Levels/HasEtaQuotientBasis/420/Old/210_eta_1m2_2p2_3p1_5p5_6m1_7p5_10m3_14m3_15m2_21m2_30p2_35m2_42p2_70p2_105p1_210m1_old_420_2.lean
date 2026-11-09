module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«210».New.«210_eta_1m2_2p2_3p1_5p5_6m1_7p5_10m3_14m3_15m2_21m2_30p2_35m2_42p2_70p2_105p1_210m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(2z)^(-2) η(4z)^2 η(6z) η(10z)^5 η(12z)^(-1) η(14z)^5 η(20z)^(-3) η(28z)^(-3) η(30z)^(-2) η(42z)^(-2) η(60z)^2 η(70z)^(-2) η(84z)^2 η(140z)^2 η(210z) η(420z)^(-1)`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_210_eta_1m2_2p2_3p1_5p5_6m1_7p5_10m3_14m3_15m2_21m2_30p2_35m2_42p2_70p2_105p1_210m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-2) η(4z)^2 η(6z) η(10z)^5 η(12z)^(-1) η(14z)^5 η(20z)^(-3) η(28z)^(-3) η(30z)^(-2) η(42z)^(-2) η(60z)^2 η(70z)^(-2) η(84z)^2 η(140z)^2 η(210z) η(420z)^(-1)` at level 420. -/
abbrev cuspForm_210_eta_1m2_2p2_3p1_5p5_6m1_7p5_10m3_14m3_15m2_21m2_30p2_35m2_42p2_70p2_105p1_210m1_old_420_2 : gamma0CuspForms 420 :=
  gamma0Rescale cuspForm_210_eta_1m2_2p2_3p1_5p5_6m1_7p5_10m3_14m3_15m2_21m2_30p2_35m2_42p2_70p2_105p1_210m1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_210_eta_1m2_2p2_3p1_5p5_6m1_7p5_10m3_14m3_15m2_21m2_30p2_35m2_42p2_70p2_105p1_210m1_old_420_2_eq_eta :
    cuspForm_210_eta_1m2_2p2_3p1_5p5_6m1_7p5_10m3_14m3_15m2_21m2_30p2_35m2_42p2_70p2_105p1_210m1_old_420_2 =
      etaQuotientCuspForm 420 sparse![420; 1 => -2, 3 => 2, 5 => 1, 9 => 5, 11 => -1, 13 => 5, 19 => -3, 27 => -3, 29 => -2, 41 => -2, 59 => 2, 69 => -2, 83 => 2, 139 => 2, 209 => 1, 419 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m2_2p2_3p1_5p5_6m1_7p5_10m3_14m3_15m2_21m2_30p2_35m2_42p2_70p2_105p1_210m1_old_420_2_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m2_2p2_3p1_5p5_6m1_7p5_10m3_14m3_15m2_21m2_30p2_35m2_42p2_70p2_105p1_210m1_old_420_2 =
    [0, 0, 1, 0, 2, 0, 3, 0, 5, 0, 7, 0, 6, 0, 6, 0, 3, 0, -3, 0,
     -7, 0, -13, 0, -20, 0, -16, 0, -12, 0, -11, 0, 4, 0, 10, 0, 12, 0, 17, 0,
     13, 0, 0, 0, 4, 0, -11, 0, -15, 0, -6, 0, -5, 0, 0, 0, 6, 0, 1, 0,
     -1, 0, 1, 0, -16, 0, 0, 0, -13, 0, 0, 0, 11, 0, 16, 0, 13, 0, 37, 0,
     10, 0, 1, 0, 6, 0, -18, 0, 0, 0, -1, 0, -7, 0, -13, 0, 23, 0, -11, 0] := by
  eta_coeff

end WeightTwoCusps
