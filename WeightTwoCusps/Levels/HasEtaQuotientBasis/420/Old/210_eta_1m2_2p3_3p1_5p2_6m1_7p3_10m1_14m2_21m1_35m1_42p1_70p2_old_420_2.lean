module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«210».New.«210_eta_1m2_2p3_3p1_5p2_6m1_7p3_10m1_14m2_21m1_35m1_42p1_70p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(2z)^(-2) η(4z)^3 η(6z) η(10z)^2 η(12z)^(-1) η(14z)^3 η(20z)^(-1) η(28z)^(-2) η(42z)^(-1) η(70z)^(-1) η(84z) η(140z)^2`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_210_eta_1m2_2p3_3p1_5p2_6m1_7p3_10m1_14m2_21m1_35m1_42p1_70p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-2) η(4z)^3 η(6z) η(10z)^2 η(12z)^(-1) η(14z)^3 η(20z)^(-1) η(28z)^(-2) η(42z)^(-1) η(70z)^(-1) η(84z) η(140z)^2` at level 420. -/
abbrev cuspForm_210_eta_1m2_2p3_3p1_5p2_6m1_7p3_10m1_14m2_21m1_35m1_42p1_70p2_old_420_2 : gamma0CuspForms 420 :=
  gamma0Rescale cuspForm_210_eta_1m2_2p3_3p1_5p2_6m1_7p3_10m1_14m2_21m1_35m1_42p1_70p2 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_210_eta_1m2_2p3_3p1_5p2_6m1_7p3_10m1_14m2_21m1_35m1_42p1_70p2_old_420_2_eq_eta :
    cuspForm_210_eta_1m2_2p3_3p1_5p2_6m1_7p3_10m1_14m2_21m1_35m1_42p1_70p2_old_420_2 =
      etaQuotientCuspForm 420 sparse![420; 1 => -2, 3 => 3, 5 => 1, 9 => 2, 11 => -1, 13 => 3, 19 => -1, 27 => -2, 41 => -1, 69 => -1, 83 => 1, 139 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m2_2p3_3p1_5p2_6m1_7p3_10m1_14m2_21m1_35m1_42p1_70p2_old_420_2_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m2_2p3_3p1_5p2_6m1_7p3_10m1_14m2_21m1_35m1_42p1_70p2_old_420_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 3, 0, 3, 0,
     2, 0, 2, 0, 0, 0, -3, 0, -3, 0, -5, 0, -6, 0, -3, 0, -3, 0, -1, 0,
     0, 0, -2, 0, -1, 0, 0, 0, -2, 0, -1, 0, -5, 0, -4, 0, 3, 0, -1, 0,
     2, 0, 4, 0, 0, 0, 2, 0, 5, 0, -2, 0, 5, 0, 4, 0, -5, 0, 0, 0,
     0, 0, 3, 0, 5, 0, 2, 0, -2, 0, 8, 0, 5, 0, 8, 0, 1, 0, -6, 0] := by
  eta_coeff

end WeightTwoCusps
