module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«77».New.«77_eta_1p1_7p1_11p1_77p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 308

The eta expression is `η(z) η(7z) η(11z) η(77z)`; see
[the local level table](../../TABLE.md#level-308).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_77_eta_1p1_7p1_11p1_77p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(7z) η(11z) η(77z)` at level 308. -/
abbrev cuspForm_77_eta_1p1_7p1_11p1_77p1_old_308_1 : gamma0CuspForms 308 :=
  gamma0RescaleToLevel cuspForm_77_eta_1p1_7p1_11p1_77p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_77_eta_1p1_7p1_11p1_77p1_old_308_1_eq_eta :
    cuspForm_77_eta_1p1_7p1_11p1_77p1_old_308_1 =
      etaQuotientCuspForm 308 sparse![308; 0 => 1, 6 => 1, 10 => 1, 76 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_77_eta_1p1_7p1_11p1_77p1_old_308_1_first_coeffs :
    first_coeffs 100 cuspForm_77_eta_1p1_7p1_11p1_77p1_old_308_1 =
    [0, 0, 0, 0, 1, -1, -1, 0, 0, 1, 0, 0, 1, 1, 0, -1, -1, 1, -2, 0,
     0, 0, 0, -1, -1, -1, 1, 3, 1, 2, 2, -2, 0, 0, -1, -1, 1, -3, 2, 0,
     0, -3, -1, 0, -1, 0, 2, 1, -1, 0, 0, 2, -1, 2, -2, 1, 0, -2, 2, 2,
     0, 1, 1, 1, -1, 2, 1, 1, -3, -3, 0, -3, -2, -1, -2, -1, 2, 0, 0, 2,
     -2, 2, -1, -2, 1, 4, 0, 0, 0, 1, 4, 1, 0, -3, -1, -2, 3, 1, 0, -1] := by
  eta_coeff

end WeightTwoCusps
