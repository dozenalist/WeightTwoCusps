module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«154».New.«154_eta_1m1_2p2_7m1_11p2_14p2_22m1_77p2_154m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 308

The eta expression is `η(2z)^(-1) η(4z)^2 η(14z)^(-1) η(22z)^2 η(28z)^2 η(44z)^(-1) η(154z)^2 η(308z)^(-1)`; see
[the local level table](../../TABLE.md#level-308).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_154_eta_1m1_2p2_7m1_11p2_14p2_22m1_77p2_154m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-1) η(4z)^2 η(14z)^(-1) η(22z)^2 η(28z)^2 η(44z)^(-1) η(154z)^2 η(308z)^(-1)` at level 308. -/
abbrev cuspForm_154_eta_1m1_2p2_7m1_11p2_14p2_22m1_77p2_154m1_old_308_2 : gamma0CuspForms 308 :=
  gamma0Rescale cuspForm_154_eta_1m1_2p2_7m1_11p2_14p2_22m1_77p2_154m1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_154_eta_1m1_2p2_7m1_11p2_14p2_22m1_77p2_154m1_old_308_2_eq_eta :
    cuspForm_154_eta_1m1_2p2_7m1_11p2_14p2_22m1_77p2_154m1_old_308_2 =
      etaQuotientCuspForm 308 sparse![308; 1 => -1, 3 => 2, 13 => -1, 21 => 2, 27 => 2, 43 => -1, 153 => 2, 307 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_154_eta_1m1_2p2_7m1_11p2_14p2_22m1_77p2_154m1_old_308_2_first_coeffs :
    first_coeffs 100 cuspForm_154_eta_1m1_2p2_7m1_11p2_14p2_22m1_77p2_154m1_old_308_2 =
    [0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0,
     0, 0, 2, 0, -2, 0, -2, 0, 1, 0, -2, 0, 1, 0, 0, 0, -1, 0, -2, 0,
     -2, 0, 0, 0, -2, 0, 2, 0, 0, 0, -1, 0, 0, 0, -2, 0, 1, 0, 0, 0,
     0, 0, 0, 0, 1, 0, -4, 0, -4, 0, 0, 0, -1, 0, 2, 0, 0, 0, -2, 0,
     -4, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 4, 0, -2, 0, -2, 0, 1, 0] := by
  eta_coeff

end WeightTwoCusps
