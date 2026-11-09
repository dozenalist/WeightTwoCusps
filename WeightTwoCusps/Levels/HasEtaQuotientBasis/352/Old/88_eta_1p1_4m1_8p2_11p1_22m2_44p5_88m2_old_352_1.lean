module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«88».New.«88_eta_1p1_4m1_8p2_11p1_22m2_44p5_88m2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 352

The eta expression is `η(z) η(4z)^(-1) η(8z)^2 η(11z) η(22z)^(-2) η(44z)^5 η(88z)^(-2)`; see
[the local level table](../../TABLE.md#level-352).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_88_eta_1p1_4m1_8p2_11p1_22m2_44p5_88m2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(4z)^(-1) η(8z)^2 η(11z) η(22z)^(-2) η(44z)^5 η(88z)^(-2)` at level 352. -/
abbrev cuspForm_88_eta_1p1_4m1_8p2_11p1_22m2_44p5_88m2_old_352_1 : gamma0CuspForms 352 :=
  gamma0RescaleToLevel cuspForm_88_eta_1p1_4m1_8p2_11p1_22m2_44p5_88m2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_88_eta_1p1_4m1_8p2_11p1_22m2_44p5_88m2_old_352_1_eq_eta :
    cuspForm_88_eta_1p1_4m1_8p2_11p1_22m2_44p5_88m2_old_352_1 =
      etaQuotientCuspForm 352 sparse![352; 0 => 1, 3 => -1, 7 => 2, 10 => 1, 21 => -2, 43 => 5, 87 => -2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_88_eta_1p1_4m1_8p2_11p1_22m2_44p5_88m2_old_352_1_first_coeffs :
    first_coeffs 100 cuspForm_88_eta_1p1_4m1_8p2_11p1_22m2_44p5_88m2_old_352_1 =
    [0, 1, -1, -1, 0, 1, 0, -1, 1, 0, 1, 0, 0, 1, 0, -1, -2, -1, 2, -1,
     0, -1, 0, 1, -1, 0, 0, 3, 0, -2, 2, 1, 2, 0, -2, 3, 0, -1, -4, 1,
     1, -3, -2, -4, 0, -4, 2, 6, 2, 1, 0, 3, 0, 0, 0, 0, -2, -1, 0, 3,
     0, 6, -6, -2, 0, -3, 1, -1, 0, 1, 4, -3, -2, 5, -1, -4, 0, -1, 4, -8,
     -2, -1, 4, -2, 0, 3, 8, 6, 1, 9, -2, -10, 0, 1, -4, -5, -2, 1, 3, -2] := by
  eta_coeff

end WeightTwoCusps
