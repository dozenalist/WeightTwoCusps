module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«210».New.«210_eta_1m2_2p2_3p1_5p5_6m1_7p5_10m3_14m3_15m2_21m2_30p2_35m2_42p2_70p2_105p1_210m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(z)^(-2) η(2z)^2 η(3z) η(5z)^5 η(6z)^(-1) η(7z)^5 η(10z)^(-3) η(14z)^(-3) η(15z)^(-2) η(21z)^(-2) η(30z)^2 η(35z)^(-2) η(42z)^2 η(70z)^2 η(105z) η(210z)^(-1)`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_210_eta_1m2_2p2_3p1_5p5_6m1_7p5_10m3_14m3_15m2_21m2_30p2_35m2_42p2_70p2_105p1_210m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z) η(5z)^5 η(6z)^(-1) η(7z)^5 η(10z)^(-3) η(14z)^(-3) η(15z)^(-2) η(21z)^(-2) η(30z)^2 η(35z)^(-2) η(42z)^2 η(70z)^2 η(105z) η(210z)^(-1)` at level 420. -/
abbrev cuspForm_210_eta_1m2_2p2_3p1_5p5_6m1_7p5_10m3_14m3_15m2_21m2_30p2_35m2_42p2_70p2_105p1_210m1_old_420_1 : gamma0CuspForms 420 :=
  gamma0RescaleToLevel cuspForm_210_eta_1m2_2p2_3p1_5p5_6m1_7p5_10m3_14m3_15m2_21m2_30p2_35m2_42p2_70p2_105p1_210m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_210_eta_1m2_2p2_3p1_5p5_6m1_7p5_10m3_14m3_15m2_21m2_30p2_35m2_42p2_70p2_105p1_210m1_old_420_1_eq_eta :
    cuspForm_210_eta_1m2_2p2_3p1_5p5_6m1_7p5_10m3_14m3_15m2_21m2_30p2_35m2_42p2_70p2_105p1_210m1_old_420_1 =
      etaQuotientCuspForm 420 sparse![420; 0 => -2, 1 => 2, 2 => 1, 4 => 5, 5 => -1, 6 => 5, 9 => -3, 13 => -3, 14 => -2, 20 => -2, 29 => 2, 34 => -2, 41 => 2, 69 => 2, 104 => 1, 209 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m2_2p2_3p1_5p5_6m1_7p5_10m3_14m3_15m2_21m2_30p2_35m2_42p2_70p2_105p1_210m1_old_420_1_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m2_2p2_3p1_5p5_6m1_7p5_10m3_14m3_15m2_21m2_30p2_35m2_42p2_70p2_105p1_210m1_old_420_1 =
    [0, 1, 2, 3, 5, 7, 6, 6, 3, -3, -7, -13, -20, -16, -12, -11, 4, 10, 12, 17,
     13, 0, 4, -11, -15, -6, -5, 0, 6, 1, -1, 1, -16, 0, -13, 0, 11, 16, 13, 37,
     10, 1, 6, -18, 0, -1, -7, -13, 23, -11, 9, -5, -7, -17, -12, -11, 7, 17, -4, 24,
     -2, 28, 23, 14, -15, 2, -24, -12, -7, -43, -9, -14, 5, 13, 44, 14, 21, -13, 5, 17,
     -16, -8, -25, -4, -3, 30, -24, -6, -28, -7, -5, 0, -7, -15, -2, -7, 36, 0, 20, -23] := by
  eta_coeff

end WeightTwoCusps
