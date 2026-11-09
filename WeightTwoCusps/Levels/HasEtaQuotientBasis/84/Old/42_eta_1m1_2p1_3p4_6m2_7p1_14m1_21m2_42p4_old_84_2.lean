module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«42».New.«42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 84

The eta expression is `η(2z)^(-1) η(4z) η(6z)^4 η(12z)^(-2) η(14z) η(28z)^(-1) η(42z)^(-2) η(84z)^4`; see
[the local level table](../../TABLE.md#level-84).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-1) η(4z) η(6z)^4 η(12z)^(-2) η(14z) η(28z)^(-1) η(42z)^(-2) η(84z)^4` at level 84. -/
abbrev cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_84_2 : gamma0CuspForms 84 :=
  gamma0Rescale cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_84_2_eq_eta :
    cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_84_2 =
      etaQuotientCuspForm 84 sparse![84; 1 => -1, 3 => 1, 5 => 4, 11 => -2, 13 => 1, 27 => -1, 41 => -2, 83 => 4] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_84_2_first_coeffs :
    first_coeffs 100 cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_84_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, -2, 0, -2, 0,
     -1, 0, 0, 0, 0, 0, -3, 0, -1, 0, 0, 0, 2, 0, 4, 0, 2, 0, 1, 0,
     1, 0, 0, 0, 4, 0, -2, 0, -1, 0, -2, 0, -1, 0, 3, 0, 1, 0, -2, 0,
     -2, 0, -2, 0, 0, 0, -2, 0, -8, 0, -1, 0, -2, 0, 2, 0, 3, 0, 2, 0,
     3, 0, 4, 0, -1, 0, 6, 0, 0, 0, 1, 0, -2, 0, -6, 0, 2, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
