module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«154».New.«154_eta_2p1_7p2_14m1_22p1_77p2_154m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 308

The eta expression is `η(2z) η(7z)^2 η(14z)^(-1) η(22z) η(77z)^2 η(154z)^(-1)`; see
[the local level table](../../TABLE.md#level-308).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_154_eta_2p1_7p2_14m1_22p1_77p2_154m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(7z)^2 η(14z)^(-1) η(22z) η(77z)^2 η(154z)^(-1)` at level 308. -/
abbrev cuspForm_154_eta_2p1_7p2_14m1_22p1_77p2_154m1_old_308_1 : gamma0CuspForms 308 :=
  gamma0RescaleToLevel cuspForm_154_eta_2p1_7p2_14m1_22p1_77p2_154m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_154_eta_2p1_7p2_14m1_22p1_77p2_154m1_old_308_1_eq_eta :
    cuspForm_154_eta_2p1_7p2_14m1_22p1_77p2_154m1_old_308_1 =
      etaQuotientCuspForm 308 sparse![308; 1 => 1, 6 => 2, 13 => -1, 21 => 1, 76 => 2, 153 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_154_eta_2p1_7p2_14m1_22p1_77p2_154m1_old_308_1_first_coeffs :
    first_coeffs 100 cuspForm_154_eta_2p1_7p2_14m1_22p1_77p2_154m1_old_308_1 =
    [0, 1, 0, -1, 0, -1, 0, 0, -2, 0, 2, 1, 2, 0, 0, 1, 0, 0, -2, 0,
     0, 0, -2, -1, 0, 0, 0, 1, 0, 2, 2, -3, 0, -3, -2, 0, 0, -1, 2, 2,
     2, 0, 0, 2, 2, 0, 0, 2, 0, 1, 0, -2, 0, 2, -4, 1, -2, 0, 0, -3,
     -4, -2, 2, 0, -2, -2, 4, -1, 2, 1, 0, -1, 0, 0, 0, 4, -2, 2, -2, 0,
     2, 3, 2, -2, 0, 4, 2, -6, 0, -5, -2, 0, -2, 1, 2, 2, 4, 1, 0, 2] := by
  eta_coeff

end WeightTwoCusps
