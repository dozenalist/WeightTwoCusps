module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«42».New.«42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 462

The eta expression is `η(11z)^(-2) η(22z)^4 η(33z) η(66z)^(-1) η(77z)^4 η(154z)^(-2) η(231z)^(-1) η(462z)`; see
[the local level table](../../TABLE.md#level-462).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(11z)` of `cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(11z)^(-2) η(22z)^4 η(33z) η(66z)^(-1) η(77z)^4 η(154z)^(-2) η(231z)^(-1) η(462z)` at level 462. -/
abbrev cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_462_11 : gamma0CuspForms 462 :=
  gamma0Rescale cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1 11

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_462_11_eq_eta :
    cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_462_11 =
      etaQuotientCuspForm 462 sparse![462; 10 => -2, 21 => 4, 32 => 1, 65 => -1, 76 => 4, 153 => -2, 230 => -1, 461 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_462_11_first_coeffs :
    first_coeffs 100 cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_462_11 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8] := by
  eta_coeff

end WeightTwoCusps
