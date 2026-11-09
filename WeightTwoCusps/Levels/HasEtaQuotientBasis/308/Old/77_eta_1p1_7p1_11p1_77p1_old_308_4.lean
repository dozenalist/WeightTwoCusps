module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«77».New.«77_eta_1p1_7p1_11p1_77p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 308

The eta expression is `η(4z) η(28z) η(44z) η(308z)`; see
[the local level table](../../TABLE.md#level-308).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_77_eta_1p1_7p1_11p1_77p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z) η(28z) η(44z) η(308z)` at level 308. -/
abbrev cuspForm_77_eta_1p1_7p1_11p1_77p1_old_308_4 : gamma0CuspForms 308 :=
  gamma0Rescale cuspForm_77_eta_1p1_7p1_11p1_77p1 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_77_eta_1p1_7p1_11p1_77p1_old_308_4_eq_eta :
    cuspForm_77_eta_1p1_7p1_11p1_77p1_old_308_4 =
      etaQuotientCuspForm 308 sparse![308; 3 => 1, 27 => 1, 43 => 1, 307 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_77_eta_1p1_7p1_11p1_77p1_old_308_4_first_coeffs :
    first_coeffs 100 cuspForm_77_eta_1p1_7p1_11p1_77p1_old_308_4 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
     -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
     -1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
