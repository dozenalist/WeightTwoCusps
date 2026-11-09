module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«154».New.«154_eta_1m1_2p2_7p1_11m1_22p2_77p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 462

The eta expression is `η(z)^(-1) η(2z)^2 η(7z) η(11z)^(-1) η(22z)^2 η(77z)`; see
[the local level table](../../TABLE.md#level-462).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_154_eta_1m1_2p2_7p1_11m1_22p2_77p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(7z) η(11z)^(-1) η(22z)^2 η(77z)` at level 462. -/
abbrev cuspForm_154_eta_1m1_2p2_7p1_11m1_22p2_77p1_old_462_1 : gamma0CuspForms 462 :=
  gamma0RescaleToLevel cuspForm_154_eta_1m1_2p2_7p1_11m1_22p2_77p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_154_eta_1m1_2p2_7p1_11m1_22p2_77p1_old_462_1_eq_eta :
    cuspForm_154_eta_1m1_2p2_7p1_11m1_22p2_77p1_old_462_1 =
      etaQuotientCuspForm 462 sparse![462; 0 => -1, 1 => 2, 6 => 1, 10 => -1, 21 => 2, 76 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_154_eta_1m1_2p2_7p1_11m1_22p2_77p1_old_462_1_first_coeffs :
    first_coeffs 100 cuspForm_154_eta_1m1_2p2_7p1_11m1_22p2_77p1_old_462_1 =
    [0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, -1, -1, 0, 0, 1, 1, -1, 0,
     0, 0, -1, -1, -1, -1, 1, -1, 0, -2, -1, 0, 0, -2, -1, 0, -1, 1, 0, 1,
     -2, 3, 0, 1, 1, -2, 0, -1, -1, 0, 2, -2, 1, 0, 2, -1, 0, 1, -2, 0,
     1, 3, -1, 0, 0, 1, 1, -2, 1, 1, 0, 4, 2, -1, 2, 1, 2, 1, -3, 1,
     0, -1, 1, 2, -1, -3, 1, 2, -2, -1, 0, -1, 0, 1, 1, 0, 1, -1, 0, 1] := by
  eta_coeff

end WeightTwoCusps
