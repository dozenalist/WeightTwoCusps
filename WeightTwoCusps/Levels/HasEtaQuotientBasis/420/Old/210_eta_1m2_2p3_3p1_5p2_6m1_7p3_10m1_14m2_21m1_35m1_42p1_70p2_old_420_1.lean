module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«210».New.«210_eta_1m2_2p3_3p1_5p2_6m1_7p3_10m1_14m2_21m1_35m1_42p1_70p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(z)^(-2) η(2z)^3 η(3z) η(5z)^2 η(6z)^(-1) η(7z)^3 η(10z)^(-1) η(14z)^(-2) η(21z)^(-1) η(35z)^(-1) η(42z) η(70z)^2`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_210_eta_1m2_2p3_3p1_5p2_6m1_7p3_10m1_14m2_21m1_35m1_42p1_70p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z) η(5z)^2 η(6z)^(-1) η(7z)^3 η(10z)^(-1) η(14z)^(-2) η(21z)^(-1) η(35z)^(-1) η(42z) η(70z)^2` at level 420. -/
abbrev cuspForm_210_eta_1m2_2p3_3p1_5p2_6m1_7p3_10m1_14m2_21m1_35m1_42p1_70p2_old_420_1 : gamma0CuspForms 420 :=
  gamma0RescaleToLevel cuspForm_210_eta_1m2_2p3_3p1_5p2_6m1_7p3_10m1_14m2_21m1_35m1_42p1_70p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_210_eta_1m2_2p3_3p1_5p2_6m1_7p3_10m1_14m2_21m1_35m1_42p1_70p2_old_420_1_eq_eta :
    cuspForm_210_eta_1m2_2p3_3p1_5p2_6m1_7p3_10m1_14m2_21m1_35m1_42p1_70p2_old_420_1 =
      etaQuotientCuspForm 420 sparse![420; 0 => -2, 1 => 3, 2 => 1, 4 => 2, 5 => -1, 6 => 3, 9 => -1, 13 => -2, 20 => -1, 34 => -1, 41 => 1, 69 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m2_2p3_3p1_5p2_6m1_7p3_10m1_14m2_21m1_35m1_42p1_70p2_old_420_1_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m2_2p3_3p1_5p2_6m1_7p3_10m1_14m2_21m1_35m1_42p1_70p2_old_420_1 =
    [0, 0, 0, 0, 0, 1, 2, 2, 3, 3, 2, 2, 0, -3, -3, -5, -6, -3, -3, -1,
     0, -2, -1, 0, -2, -1, -5, -4, 3, -1, 2, 4, 0, 2, 5, -2, 5, 4, -5, 0,
     0, 3, 5, 2, -2, 8, 5, 8, 1, -6, 1, -3, -7, -1, 1, -7, 5, -6, 1, 8,
     -3, -3, 5, 6, 10, 9, -4, 4, -1, 1, -3, -8, -4, 0, 2, 5, 3, -7, -4, -9,
     -1, -5, -9, -6, -4, 4, 3, 8, 1, -1, -7, 1, 2, 7, -7, -10, 2, 10, 9, -2] := by
  eta_coeff

end WeightTwoCusps
