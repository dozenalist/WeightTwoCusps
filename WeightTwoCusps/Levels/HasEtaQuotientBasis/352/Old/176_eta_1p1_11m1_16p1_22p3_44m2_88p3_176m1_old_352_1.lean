module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«176».New.«176_eta_1p1_11m1_16p1_22p3_44m2_88p3_176m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 352

The eta expression is `η(z) η(11z)^(-1) η(16z) η(22z)^3 η(44z)^(-2) η(88z)^3 η(176z)^(-1)`; see
[the local level table](../../TABLE.md#level-352).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_176_eta_1p1_11m1_16p1_22p3_44m2_88p3_176m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(11z)^(-1) η(16z) η(22z)^3 η(44z)^(-2) η(88z)^3 η(176z)^(-1)` at level 352. -/
abbrev cuspForm_176_eta_1p1_11m1_16p1_22p3_44m2_88p3_176m1_old_352_1 : gamma0CuspForms 352 :=
  gamma0RescaleToLevel cuspForm_176_eta_1p1_11m1_16p1_22p3_44m2_88p3_176m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_176_eta_1p1_11m1_16p1_22p3_44m2_88p3_176m1_old_352_1_eq_eta :
    cuspForm_176_eta_1p1_11m1_16p1_22p3_44m2_88p3_176m1_old_352_1 =
      etaQuotientCuspForm 352 sparse![352; 0 => 1, 10 => -1, 15 => 1, 21 => 3, 43 => -2, 87 => 3, 175 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_176_eta_1p1_11m1_16p1_22p3_44m2_88p3_176m1_old_352_1_first_coeffs :
    first_coeffs 100 cuspForm_176_eta_1p1_11m1_16p1_22p3_44m2_88p3_176m1_old_352_1 =
    [0, 0, 0, 1, -1, -1, 0, 0, 1, 0, 1, 0, 0, 0, 1, -2, -1, 0, -1, 0,
     1, 2, 0, 0, -1, 0, -1, 1, 0, 0, -2, 2, 0, 0, 1, -2, 2, 1, -1, 0,
     1, 0, -1, -2, 0, 0, 0, 2, 1, -2, 1, -2, 0, -2, 2, 0, -2, 0, 0, -1,
     2, 0, 0, 0, 2, 4, 0, 1, -2, -1, 1, 2, -2, 0, -1, 2, -4, 0, 1, 0,
     -1, 2, -1, 2, -2, -2, -2, -4, 1, 0, 2, -2, 2, 1, 2, 0, 0, -4, 0, 1] := by
  eta_coeff

end WeightTwoCusps
