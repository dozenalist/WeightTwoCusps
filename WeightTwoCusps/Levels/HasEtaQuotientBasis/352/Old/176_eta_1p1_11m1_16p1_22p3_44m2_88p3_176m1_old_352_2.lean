module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«176».New.«176_eta_1p1_11m1_16p1_22p3_44m2_88p3_176m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 352

The eta expression is `η(2z) η(22z)^(-1) η(32z) η(44z)^3 η(88z)^(-2) η(176z)^3 η(352z)^(-1)`; see
[the local level table](../../TABLE.md#level-352).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_176_eta_1p1_11m1_16p1_22p3_44m2_88p3_176m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(22z)^(-1) η(32z) η(44z)^3 η(88z)^(-2) η(176z)^3 η(352z)^(-1)` at level 352. -/
abbrev cuspForm_176_eta_1p1_11m1_16p1_22p3_44m2_88p3_176m1_old_352_2 : gamma0CuspForms 352 :=
  gamma0Rescale cuspForm_176_eta_1p1_11m1_16p1_22p3_44m2_88p3_176m1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_176_eta_1p1_11m1_16p1_22p3_44m2_88p3_176m1_old_352_2_eq_eta :
    cuspForm_176_eta_1p1_11m1_16p1_22p3_44m2_88p3_176m1_old_352_2 =
      etaQuotientCuspForm 352 sparse![352; 1 => 1, 21 => -1, 31 => 1, 43 => 3, 87 => -2, 175 => 3, 351 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_176_eta_1p1_11m1_16p1_22p3_44m2_88p3_176m1_old_352_2_first_coeffs :
    first_coeffs 100 cuspForm_176_eta_1p1_11m1_16p1_22p3_44m2_88p3_176m1_old_352_2 =
    [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0, 1, 0, -2, 0, -1, 0, 0, 0, -1, 0, 0, 0,
     1, 0, 2, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0,
     -2, 0, 2, 0, 0, 0, 0, 0, 1, 0, -2, 0, 2, 0, 1, 0, -1, 0, 0, 0,
     1, 0, 0, 0, -1, 0, -2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, -2, 0] := by
  eta_coeff

end WeightTwoCusps
