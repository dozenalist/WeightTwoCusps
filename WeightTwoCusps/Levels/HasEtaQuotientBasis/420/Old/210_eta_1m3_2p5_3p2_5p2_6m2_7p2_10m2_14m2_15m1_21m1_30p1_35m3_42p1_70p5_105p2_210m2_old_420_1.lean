module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«210».New.«210_eta_1m3_2p5_3p2_5p2_6m2_7p2_10m2_14m2_15m1_21m1_30p1_35m3_42p1_70p5_105p2_210m2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(z)^(-3) η(2z)^5 η(3z)^2 η(5z)^2 η(6z)^(-2) η(7z)^2 η(10z)^(-2) η(14z)^(-2) η(15z)^(-1) η(21z)^(-1) η(30z) η(35z)^(-3) η(42z) η(70z)^5 η(105z)^2 η(210z)^(-2)`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_210_eta_1m3_2p5_3p2_5p2_6m2_7p2_10m2_14m2_15m1_21m1_30p1_35m3_42p1_70p5_105p2_210m2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^5 η(3z)^2 η(5z)^2 η(6z)^(-2) η(7z)^2 η(10z)^(-2) η(14z)^(-2) η(15z)^(-1) η(21z)^(-1) η(30z) η(35z)^(-3) η(42z) η(70z)^5 η(105z)^2 η(210z)^(-2)` at level 420. -/
abbrev cuspForm_210_eta_1m3_2p5_3p2_5p2_6m2_7p2_10m2_14m2_15m1_21m1_30p1_35m3_42p1_70p5_105p2_210m2_old_420_1 : gamma0CuspForms 420 :=
  gamma0RescaleToLevel cuspForm_210_eta_1m3_2p5_3p2_5p2_6m2_7p2_10m2_14m2_15m1_21m1_30p1_35m3_42p1_70p5_105p2_210m2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_210_eta_1m3_2p5_3p2_5p2_6m2_7p2_10m2_14m2_15m1_21m1_30p1_35m3_42p1_70p5_105p2_210m2_old_420_1_eq_eta :
    cuspForm_210_eta_1m3_2p5_3p2_5p2_6m2_7p2_10m2_14m2_15m1_21m1_30p1_35m3_42p1_70p5_105p2_210m2_old_420_1 =
      etaQuotientCuspForm 420 sparse![420; 0 => -3, 1 => 5, 2 => 2, 4 => 2, 5 => -2, 6 => 2, 9 => -2, 13 => -2, 14 => -1, 20 => -1, 29 => 1, 34 => -3, 41 => 1, 69 => 5, 104 => 2, 209 => -2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m3_2p5_3p2_5p2_6m2_7p2_10m2_14m2_15m1_21m1_30p1_35m3_42p1_70p5_105p2_210m2_old_420_1_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m3_2p5_3p2_5p2_6m2_7p2_10m2_14m2_15m1_21m1_30p1_35m3_42p1_70p5_105p2_210m2_old_420_1 =
    [0, 0, 1, 3, 4, 5, 5, 3, 2, 0, -3, -6, -8, -7, -5, -2, 3, 5, 3, 4,
     1, -2, -1, -5, -8, -5, -1, 2, 4, 0, -1, -3, -2, -1, -4, -1, 4, 3, 5, 16,
     6, 5, 5, -2, 0, 3, -5, -10, -6, -6, 3, -8, -5, -7, -8, -2, 4, -4, 0, 4,
     -6, 15, 8, 5, -6, -3, -13, -2, -7, -12, -6, -12, 10, 11, 20, 7, 15, -4, 16, 10,
     -2, -10, -15, 0, -1, 9, -16, 2, -16, 3, -5, 1, -2, -2, -2, 5, 35, 2, 10, -16] := by
  eta_coeff

end WeightTwoCusps
