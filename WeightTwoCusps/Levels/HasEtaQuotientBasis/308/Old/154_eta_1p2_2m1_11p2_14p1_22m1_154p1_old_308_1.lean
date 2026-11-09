module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«154».New.«154_eta_1p2_2m1_11p2_14p1_22m1_154p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 308

The eta expression is `η(z)^2 η(2z)^(-1) η(11z)^2 η(14z) η(22z)^(-1) η(154z)`; see
[the local level table](../../TABLE.md#level-308).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_154_eta_1p2_2m1_11p2_14p1_22m1_154p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^2 η(2z)^(-1) η(11z)^2 η(14z) η(22z)^(-1) η(154z)` at level 308. -/
abbrev cuspForm_154_eta_1p2_2m1_11p2_14p1_22m1_154p1_old_308_1 : gamma0CuspForms 308 :=
  gamma0RescaleToLevel cuspForm_154_eta_1p2_2m1_11p2_14p1_22m1_154p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_154_eta_1p2_2m1_11p2_14p1_22m1_154p1_old_308_1_eq_eta :
    cuspForm_154_eta_1p2_2m1_11p2_14p1_22m1_154p1_old_308_1 =
      etaQuotientCuspForm 308 sparse![308; 0 => 2, 1 => -1, 10 => 2, 13 => 1, 21 => -1, 153 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_154_eta_1p2_2m1_11p2_14p1_22m1_154p1_old_308_1_first_coeffs :
    first_coeffs 100 cuspForm_154_eta_1p2_2m1_11p2_14p1_22m1_154p1_old_308_1 =
    [0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0, 2, 0, 0, 0, 0, -2, 0, -2, 4,
     0, -1, -2, 2, 0, -2, 0, 4, 0, 0, 2, 0, 0, -4, -4, -1, 6, -2, 0, -2,
     0, -4, 0, 6, 2, 0, 4, -4, 4, 0, 4, 0, -4, 0, -4, 0, -2, -6, 0, 0,
     -2, 0, 4, 0, 0, -2, 4, 8, 4, -4, 2, -4, 0, 0, 4, 0, -4, 1, -2, -2,
     4, -6, 0, -4, 2, -2, -2, 4, 0, 4, 4, 0, -4, 2, 0, -8, 4, 4, 0, 2] := by
  eta_coeff

end WeightTwoCusps
