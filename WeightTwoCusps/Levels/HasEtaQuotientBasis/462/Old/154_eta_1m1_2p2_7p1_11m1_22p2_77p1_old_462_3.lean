module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«154».New.«154_eta_1m1_2p2_7p1_11m1_22p2_77p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 462

The eta expression is `η(3z)^(-1) η(6z)^2 η(21z) η(33z)^(-1) η(66z)^2 η(231z)`; see
[the local level table](../../TABLE.md#level-462).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_154_eta_1m1_2p2_7p1_11m1_22p2_77p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-1) η(6z)^2 η(21z) η(33z)^(-1) η(66z)^2 η(231z)` at level 462. -/
abbrev cuspForm_154_eta_1m1_2p2_7p1_11m1_22p2_77p1_old_462_3 : gamma0CuspForms 462 :=
  gamma0Rescale cuspForm_154_eta_1m1_2p2_7p1_11m1_22p2_77p1 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_154_eta_1m1_2p2_7p1_11m1_22p2_77p1_old_462_3_eq_eta :
    cuspForm_154_eta_1m1_2p2_7p1_11m1_22p2_77p1_old_462_3 =
      etaQuotientCuspForm 462 sparse![462; 2 => -1, 5 => 2, 20 => 1, 32 => -1, 65 => 2, 230 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_154_eta_1m1_2p2_7p1_11m1_22p2_77p1_old_462_3_first_coeffs :
    first_coeffs 100 cuspForm_154_eta_1m1_2p2_7p1_11m1_22p2_77p1_old_462_3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, -1,
     0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0, 1, 0,
     0, -1, 0, 0, 0, 0, 0, -2, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -2] := by
  eta_coeff

end WeightTwoCusps
