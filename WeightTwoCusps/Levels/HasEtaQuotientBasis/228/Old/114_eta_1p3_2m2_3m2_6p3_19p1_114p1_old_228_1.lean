module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«114».New.«114_eta_1p3_2m2_3m2_6p3_19p1_114p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 228

The eta expression is `η(z)^3 η(2z)^(-2) η(3z)^(-2) η(6z)^3 η(19z) η(114z)`; see
[the local level table](../../TABLE.md#level-228).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_114_eta_1p3_2m2_3m2_6p3_19p1_114p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^3 η(2z)^(-2) η(3z)^(-2) η(6z)^3 η(19z) η(114z)` at level 228. -/
abbrev cuspForm_114_eta_1p3_2m2_3m2_6p3_19p1_114p1_old_228_1 : gamma0CuspForms 228 :=
  gamma0RescaleToLevel cuspForm_114_eta_1p3_2m2_3m2_6p3_19p1_114p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_114_eta_1p3_2m2_3m2_6p3_19p1_114p1_old_228_1_eq_eta :
    cuspForm_114_eta_1p3_2m2_3m2_6p3_19p1_114p1_old_228_1 =
      etaQuotientCuspForm 228 sparse![228; 0 => 3, 1 => -2, 2 => -2, 5 => 3, 18 => 1, 113 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_114_eta_1p3_2m2_3m2_6p3_19p1_114p1_old_228_1_first_coeffs :
    first_coeffs 100 cuspForm_114_eta_1p3_2m2_3m2_6p3_19p1_114p1_old_228_1 =
    [0, 0, 0, 0, 0, 0, 1, -3, 2, 1, -1, -1, 3, -1, 0, -2, -2, 2, 0, 0,
     1, 3, 0, -2, -2, 0, 2, -2, 1, 2, 0, -3, -2, -1, 0, 5, -2, 3, 0, 0,
     -1, 0, -1, 2, -2, 3, -1, -6, -1, 5, -4, 5, 1, 4, -2, 0, -6, 0, -1, -4,
     -1, 4, 5, -4, 2, 0, 3, 4, -1, -1, 2, 0, 2, -3, -5, -1, 0, -5, -3, 1,
     5, -1, 6, 2, -2, 0, -4, -4, 4, -2, -1, 0, 4, 0, 5, 0, 2, -4, 4, 2] := by
  eta_coeff

end WeightTwoCusps
