module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«154».New.«154_eta_1m1_2p2_7p1_11m1_22p2_77p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 308

The eta expression is `η(2z)^(-1) η(4z)^2 η(14z) η(22z)^(-1) η(44z)^2 η(154z)`; see
[the local level table](../../TABLE.md#level-308).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_154_eta_1m1_2p2_7p1_11m1_22p2_77p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-1) η(4z)^2 η(14z) η(22z)^(-1) η(44z)^2 η(154z)` at level 308. -/
abbrev cuspForm_154_eta_1m1_2p2_7p1_11m1_22p2_77p1_old_308_2 : gamma0CuspForms 308 :=
  gamma0Rescale cuspForm_154_eta_1m1_2p2_7p1_11m1_22p2_77p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_154_eta_1m1_2p2_7p1_11m1_22p2_77p1_old_308_2_eq_eta :
    cuspForm_154_eta_1m1_2p2_7p1_11m1_22p2_77p1_old_308_2 =
      etaQuotientCuspForm 308 sparse![308; 1 => -1, 3 => 2, 13 => 1, 21 => -1, 43 => 2, 153 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_154_eta_1m1_2p2_7p1_11m1_22p2_77p1_old_308_2_first_coeffs :
    first_coeffs 100 cuspForm_154_eta_1m1_2p2_7p1_11m1_22p2_77p1_old_308_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0,
     0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, 0, 0,
     0, 0, 0, 0, -1, 0, -1, 0, -1, 0, -1, 0, 1, 0, -1, 0, 0, 0, -2, 0,
     -1, 0, 0, 0, 0, 0, -2, 0, -1, 0, 0, 0, -1, 0, 1, 0, 0, 0, 1, 0,
     -2, 0, 3, 0, 0, 0, 1, 0, 1, 0, -2, 0, 0, 0, -1, 0, -1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
