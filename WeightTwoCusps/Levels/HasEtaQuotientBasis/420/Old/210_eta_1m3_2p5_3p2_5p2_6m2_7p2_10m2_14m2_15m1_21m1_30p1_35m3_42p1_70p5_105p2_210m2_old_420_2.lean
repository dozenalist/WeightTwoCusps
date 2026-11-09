module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«210».New.«210_eta_1m3_2p5_3p2_5p2_6m2_7p2_10m2_14m2_15m1_21m1_30p1_35m3_42p1_70p5_105p2_210m2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(2z)^(-3) η(4z)^5 η(6z)^2 η(10z)^2 η(12z)^(-2) η(14z)^2 η(20z)^(-2) η(28z)^(-2) η(30z)^(-1) η(42z)^(-1) η(60z) η(70z)^(-3) η(84z) η(140z)^5 η(210z)^2 η(420z)^(-2)`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_210_eta_1m3_2p5_3p2_5p2_6m2_7p2_10m2_14m2_15m1_21m1_30p1_35m3_42p1_70p5_105p2_210m2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-3) η(4z)^5 η(6z)^2 η(10z)^2 η(12z)^(-2) η(14z)^2 η(20z)^(-2) η(28z)^(-2) η(30z)^(-1) η(42z)^(-1) η(60z) η(70z)^(-3) η(84z) η(140z)^5 η(210z)^2 η(420z)^(-2)` at level 420. -/
abbrev cuspForm_210_eta_1m3_2p5_3p2_5p2_6m2_7p2_10m2_14m2_15m1_21m1_30p1_35m3_42p1_70p5_105p2_210m2_old_420_2 : gamma0CuspForms 420 :=
  gamma0Rescale cuspForm_210_eta_1m3_2p5_3p2_5p2_6m2_7p2_10m2_14m2_15m1_21m1_30p1_35m3_42p1_70p5_105p2_210m2 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_210_eta_1m3_2p5_3p2_5p2_6m2_7p2_10m2_14m2_15m1_21m1_30p1_35m3_42p1_70p5_105p2_210m2_old_420_2_eq_eta :
    cuspForm_210_eta_1m3_2p5_3p2_5p2_6m2_7p2_10m2_14m2_15m1_21m1_30p1_35m3_42p1_70p5_105p2_210m2_old_420_2 =
      etaQuotientCuspForm 420 sparse![420; 1 => -3, 3 => 5, 5 => 2, 9 => 2, 11 => -2, 13 => 2, 19 => -2, 27 => -2, 29 => -1, 41 => -1, 59 => 1, 69 => -3, 83 => 1, 139 => 5, 209 => 2, 419 => -2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m3_2p5_3p2_5p2_6m2_7p2_10m2_14m2_15m1_21m1_30p1_35m3_42p1_70p5_105p2_210m2_old_420_2_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m3_2p5_3p2_5p2_6m2_7p2_10m2_14m2_15m1_21m1_30p1_35m3_42p1_70p5_105p2_210m2_old_420_2 =
    [0, 0, 0, 0, 1, 0, 3, 0, 4, 0, 5, 0, 5, 0, 3, 0, 2, 0, 0, 0,
     -3, 0, -6, 0, -8, 0, -7, 0, -5, 0, -2, 0, 3, 0, 5, 0, 3, 0, 4, 0,
     1, 0, -2, 0, -1, 0, -5, 0, -8, 0, -5, 0, -1, 0, 2, 0, 4, 0, 0, 0,
     -1, 0, -3, 0, -2, 0, -1, 0, -4, 0, -1, 0, 4, 0, 3, 0, 5, 0, 16, 0,
     6, 0, 5, 0, 5, 0, -2, 0, 0, 0, 3, 0, -5, 0, -10, 0, -6, 0, -6, 0] := by
  eta_coeff

end WeightTwoCusps
