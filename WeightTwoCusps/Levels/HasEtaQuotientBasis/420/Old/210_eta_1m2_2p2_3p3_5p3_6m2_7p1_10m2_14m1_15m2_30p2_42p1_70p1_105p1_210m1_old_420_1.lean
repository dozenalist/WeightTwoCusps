module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«210».New.«210_eta_1m2_2p2_3p3_5p3_6m2_7p1_10m2_14m1_15m2_30p2_42p1_70p1_105p1_210m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^3 η(5z)^3 η(6z)^(-2) η(7z) η(10z)^(-2) η(14z)^(-1) η(15z)^(-2) η(30z)^2 η(42z) η(70z) η(105z) η(210z)^(-1)`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_210_eta_1m2_2p2_3p3_5p3_6m2_7p1_10m2_14m1_15m2_30p2_42p1_70p1_105p1_210m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^3 η(5z)^3 η(6z)^(-2) η(7z) η(10z)^(-2) η(14z)^(-1) η(15z)^(-2) η(30z)^2 η(42z) η(70z) η(105z) η(210z)^(-1)` at level 420. -/
abbrev cuspForm_210_eta_1m2_2p2_3p3_5p3_6m2_7p1_10m2_14m1_15m2_30p2_42p1_70p1_105p1_210m1_old_420_1 : gamma0CuspForms 420 :=
  gamma0RescaleToLevel cuspForm_210_eta_1m2_2p2_3p3_5p3_6m2_7p1_10m2_14m1_15m2_30p2_42p1_70p1_105p1_210m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_210_eta_1m2_2p2_3p3_5p3_6m2_7p1_10m2_14m1_15m2_30p2_42p1_70p1_105p1_210m1_old_420_1_eq_eta :
    cuspForm_210_eta_1m2_2p2_3p3_5p3_6m2_7p1_10m2_14m1_15m2_30p2_42p1_70p1_105p1_210m1_old_420_1 =
      etaQuotientCuspForm 420 sparse![420; 0 => -2, 1 => 2, 2 => 3, 4 => 3, 5 => -2, 6 => 1, 9 => -2, 13 => -1, 14 => -2, 29 => 2, 41 => 1, 69 => 1, 104 => 1, 209 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m2_2p2_3p3_5p3_6m2_7p1_10m2_14m1_15m2_30p2_42p1_70p1_105p1_210m1_old_420_1_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m2_2p2_3p3_5p3_6m2_7p1_10m2_14m1_15m2_30p2_42p1_70p1_105p1_210m1_old_420_1 =
    [0, 1, 2, 3, 3, 3, 2, 0, -1, -1, -1, -3, -2, -2, 0, 1, 4, 4, 2, 1,
     1, 0, -2, -1, -5, -4, -5, 0, 0, 1, -3, -1, 0, 2, 3, 0, 1, -8, -5, -3,
     0, -7, 0, -2, -2, -1, 5, 3, -3, 1, 1, 1, -7, 3, -6, -1, -1, 3, -2, 0,
     0, 2, 9, 0, 3, -2, 0, -8, -3, -7, -1, -10, 7, 9, 2, 4, 5, 1, -5, 11,
     -2, 0, -11, 2, -1, 0, -4, 4, -6, 1, 5, 0, 7, 5, 12, 5, 12, -14, 2, -11] := by
  eta_coeff

end WeightTwoCusps
