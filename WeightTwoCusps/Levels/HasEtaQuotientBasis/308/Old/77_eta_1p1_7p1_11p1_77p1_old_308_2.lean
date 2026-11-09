module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«77».New.«77_eta_1p1_7p1_11p1_77p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 308

The eta expression is `η(2z) η(14z) η(22z) η(154z)`; see
[the local level table](../../TABLE.md#level-308).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_77_eta_1p1_7p1_11p1_77p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(14z) η(22z) η(154z)` at level 308. -/
abbrev cuspForm_77_eta_1p1_7p1_11p1_77p1_old_308_2 : gamma0CuspForms 308 :=
  gamma0RescaleToLevel cuspForm_77_eta_1p1_7p1_11p1_77p1 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_77_eta_1p1_7p1_11p1_77p1_old_308_2_eq_eta :
    cuspForm_77_eta_1p1_7p1_11p1_77p1_old_308_2 =
      etaQuotientCuspForm 308 sparse![308; 1 => 1, 13 => 1, 21 => 1, 153 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_77_eta_1p1_7p1_11p1_77p1_old_308_2_first_coeffs :
    first_coeffs 100 cuspForm_77_eta_1p1_7p1_11p1_77p1_old_308_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1, 0,
     0, 0, 0, 0, 1, 0, 1, 0, 0, 0, -1, 0, -1, 0, 1, 0, -2, 0, 0, 0,
     0, 0, 0, 0, 0, 0, -1, 0, -1, 0, -1, 0, 1, 0, 3, 0, 1, 0, 2, 0,
     2, 0, -2, 0, 0, 0, 0, 0, -1, 0, -1, 0, 1, 0, -3, 0, 2, 0, 0, 0,
     0, 0, -3, 0, -1, 0, 0, 0, -1, 0, 0, 0, 2, 0, 1, 0, -1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
