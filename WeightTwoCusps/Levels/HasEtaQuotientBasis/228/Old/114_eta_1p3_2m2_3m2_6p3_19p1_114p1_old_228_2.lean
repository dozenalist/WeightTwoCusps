module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«114».New.«114_eta_1p3_2m2_3m2_6p3_19p1_114p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 228

The eta expression is `η(2z)^3 η(4z)^(-2) η(6z)^(-2) η(12z)^3 η(38z) η(228z)`; see
[the local level table](../../TABLE.md#level-228).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_114_eta_1p3_2m2_3m2_6p3_19p1_114p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^3 η(4z)^(-2) η(6z)^(-2) η(12z)^3 η(38z) η(228z)` at level 228. -/
abbrev cuspForm_114_eta_1p3_2m2_3m2_6p3_19p1_114p1_old_228_2 : gamma0CuspForms 228 :=
  gamma0Rescale cuspForm_114_eta_1p3_2m2_3m2_6p3_19p1_114p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_114_eta_1p3_2m2_3m2_6p3_19p1_114p1_old_228_2_eq_eta :
    cuspForm_114_eta_1p3_2m2_3m2_6p3_19p1_114p1_old_228_2 =
      etaQuotientCuspForm 228 sparse![228; 1 => 3, 3 => -2, 5 => -2, 11 => 3, 37 => 1, 227 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_114_eta_1p3_2m2_3m2_6p3_19p1_114p1_old_228_2_first_coeffs :
    first_coeffs 100 cuspForm_114_eta_1p3_2m2_3m2_6p3_19p1_114p1_old_228_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -3, 0, 2, 0, 1, 0,
     -1, 0, -1, 0, 3, 0, -1, 0, 0, 0, -2, 0, -2, 0, 2, 0, 0, 0, 0, 0,
     1, 0, 3, 0, 0, 0, -2, 0, -2, 0, 0, 0, 2, 0, -2, 0, 1, 0, 2, 0,
     0, 0, -3, 0, -2, 0, -1, 0, 0, 0, 5, 0, -2, 0, 3, 0, 0, 0, 0, 0,
     -1, 0, 0, 0, -1, 0, 2, 0, -2, 0, 3, 0, -1, 0, -6, 0, -1, 0, 5, 0] := by
  eta_coeff

end WeightTwoCusps
