module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«210».New.«210_eta_1m2_2p1_3p4_5p4_6m2_7p1_10m2_15m2_21m1_30p1_35m1_42p1_70p1_105p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(2z)^(-2) η(4z) η(6z)^4 η(10z)^4 η(12z)^(-2) η(14z) η(20z)^(-2) η(30z)^(-2) η(42z)^(-1) η(60z) η(70z)^(-1) η(84z) η(140z) η(210z)`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_210_eta_1m2_2p1_3p4_5p4_6m2_7p1_10m2_15m2_21m1_30p1_35m1_42p1_70p1_105p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-2) η(4z) η(6z)^4 η(10z)^4 η(12z)^(-2) η(14z) η(20z)^(-2) η(30z)^(-2) η(42z)^(-1) η(60z) η(70z)^(-1) η(84z) η(140z) η(210z)` at level 420. -/
abbrev cuspForm_210_eta_1m2_2p1_3p4_5p4_6m2_7p1_10m2_15m2_21m1_30p1_35m1_42p1_70p1_105p1_old_420_2 : gamma0CuspForms 420 :=
  gamma0Rescale cuspForm_210_eta_1m2_2p1_3p4_5p4_6m2_7p1_10m2_15m2_21m1_30p1_35m1_42p1_70p1_105p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_210_eta_1m2_2p1_3p4_5p4_6m2_7p1_10m2_15m2_21m1_30p1_35m1_42p1_70p1_105p1_old_420_2_eq_eta :
    cuspForm_210_eta_1m2_2p1_3p4_5p4_6m2_7p1_10m2_15m2_21m1_30p1_35m1_42p1_70p1_105p1_old_420_2 =
      etaQuotientCuspForm 420 sparse![420; 1 => -2, 3 => 1, 5 => 4, 9 => 4, 11 => -2, 13 => 1, 19 => -2, 29 => -2, 41 => -1, 59 => 1, 69 => -1, 83 => 1, 139 => 1, 209 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m2_2p1_3p4_5p4_6m2_7p1_10m2_15m2_21m1_30p1_35m1_42p1_70p1_105p1_old_420_2_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m2_2p1_3p4_5p4_6m2_7p1_10m2_15m2_21m1_30p1_35m1_42p1_70p1_105p1_old_420_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 4, 0,
     4, 0, 6, 0, 4, 0, 4, 0, -1, 0, 2, 0, -2, 0, 0, 0, -6, 0, 0, 0,
     -4, 0, -1, 0, -4, 0, 4, 0, 0, 0, -2, 0, -4, 0, 0, 0, 1, 0, -4, 0,
     0, 0, 0, 0, 4, 0, -4, 0, 4, 0, -1, 0, 0, 0, -16, 0, -12, 0, -8, 0,
     -4, 0, -4, 0, 1, 0, 6, 0, 0, 0, 4, 0, 4, 0, 12, 0, -4, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
