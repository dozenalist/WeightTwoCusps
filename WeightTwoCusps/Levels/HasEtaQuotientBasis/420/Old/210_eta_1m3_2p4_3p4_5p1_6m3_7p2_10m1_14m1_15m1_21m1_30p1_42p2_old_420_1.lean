module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«210».New.«210_eta_1m3_2p4_3p4_5p1_6m3_7p2_10m1_14m1_15m1_21m1_30p1_42p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(z)^(-3) η(2z)^4 η(3z)^4 η(5z) η(6z)^(-3) η(7z)^2 η(10z)^(-1) η(14z)^(-1) η(15z)^(-1) η(21z)^(-1) η(30z) η(42z)^2`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_210_eta_1m3_2p4_3p4_5p1_6m3_7p2_10m1_14m1_15m1_21m1_30p1_42p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^4 η(3z)^4 η(5z) η(6z)^(-3) η(7z)^2 η(10z)^(-1) η(14z)^(-1) η(15z)^(-1) η(21z)^(-1) η(30z) η(42z)^2` at level 420. -/
abbrev cuspForm_210_eta_1m3_2p4_3p4_5p1_6m3_7p2_10m1_14m1_15m1_21m1_30p1_42p2_old_420_1 : gamma0CuspForms 420 :=
  gamma0RescaleToLevel cuspForm_210_eta_1m3_2p4_3p4_5p1_6m3_7p2_10m1_14m1_15m1_21m1_30p1_42p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_210_eta_1m3_2p4_3p4_5p1_6m3_7p2_10m1_14m1_15m1_21m1_30p1_42p2_old_420_1_eq_eta :
    cuspForm_210_eta_1m3_2p4_3p4_5p1_6m3_7p2_10m1_14m1_15m1_21m1_30p1_42p2_old_420_1 =
      etaQuotientCuspForm 420 sparse![420; 0 => -3, 1 => 4, 2 => 4, 4 => 1, 5 => -3, 6 => 2, 9 => -1, 13 => -1, 14 => -1, 20 => -1, 29 => 1, 41 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m3_2p4_3p4_5p1_6m3_7p2_10m1_14m1_15m1_21m1_30p1_42p2_old_420_1_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m3_2p4_3p4_5p1_6m3_7p2_10m1_14m1_15m1_21m1_30p1_42p2_old_420_1 =
    [0, 0, 0, 1, 3, 5, 6, 5, 5, 5, 5, 4, -1, -4, -5, -2, 2, 1, 0, -1,
     -1, 4, 4, 1, -4, -10, -4, 1, 7, 5, -2, -5, -4, 0, 1, -5, -17, -17, -11, 2,
     5, 4, -6, -10, -4, 5, 1, -10, -17, -20, -10, -7, 10, -5, -4, -8, -5, 10, 5, -1,
     -8, -14, -5, 5, 3, 13, -10, 10, 3, 4, 0, 1, -5, -13, 3, 4, 11, 6, 27, 12,
     11, 5, 14, 6, 6, -2, 0, -7, 4, 6, -5, 9, -19, 10, -10, 2, 12, 11, 20, -1] := by
  eta_coeff

end WeightTwoCusps
