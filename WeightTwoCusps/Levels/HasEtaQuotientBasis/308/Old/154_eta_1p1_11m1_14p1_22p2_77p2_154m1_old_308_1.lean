module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«154».New.«154_eta_1p1_11m1_14p1_22p2_77p2_154m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 308

The eta expression is `η(z) η(11z)^(-1) η(14z) η(22z)^2 η(77z)^2 η(154z)^(-1)`; see
[the local level table](../../TABLE.md#level-308).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_154_eta_1p1_11m1_14p1_22p2_77p2_154m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(11z)^(-1) η(14z) η(22z)^2 η(77z)^2 η(154z)^(-1)` at level 308. -/
abbrev cuspForm_154_eta_1p1_11m1_14p1_22p2_77p2_154m1_old_308_1 : gamma0CuspForms 308 :=
  gamma0RescaleToLevel cuspForm_154_eta_1p1_11m1_14p1_22p2_77p2_154m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_154_eta_1p1_11m1_14p1_22p2_77p2_154m1_old_308_1_eq_eta :
    cuspForm_154_eta_1p1_11m1_14p1_22p2_77p2_154m1_old_308_1 =
      etaQuotientCuspForm 308 sparse![308; 0 => 1, 10 => -1, 13 => 1, 21 => 2, 76 => 2, 153 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_154_eta_1p1_11m1_14p1_22p2_77p2_154m1_old_308_1_first_coeffs :
    first_coeffs 100 cuspForm_154_eta_1p1_11m1_14p1_22p2_77p2_154m1_old_308_1 =
    [0, 0, 1, -1, -1, 0, 0, 1, 0, 1, 0, 0, 0, 1, -2, -1, -1, 0, 2, 0,
     1, -1, 0, -1, 1, -1, 0, -1, 2, 1, -1, 2, 0, 0, -1, 1, -1, -3, -1, 2,
     1, -1, 2, 1, 0, 1, -1, -1, -2, -2, 0, 2, -1, 0, -1, 0, 0, 1, 0, 1,
     0, 2, 1, -2, 3, 2, 0, -1, 0, -1, -1, -1, 0, -1, -1, 0, 1, 1, 0, -2,
     1, 2, -1, 0, -3, -2, 0, -3, 1, -1, -1, 4, 2, 3, 4, -5, -1, 1, 3, 0] := by
  eta_coeff

end WeightTwoCusps
