module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«88».New.«88_eta_1p1_4m1_8p2_11p1_22m2_44p5_88m2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 352

The eta expression is `η(4z) η(16z)^(-1) η(32z)^2 η(44z) η(88z)^(-2) η(176z)^5 η(352z)^(-2)`; see
[the local level table](../../TABLE.md#level-352).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_88_eta_1p1_4m1_8p2_11p1_22m2_44p5_88m2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z) η(16z)^(-1) η(32z)^2 η(44z) η(88z)^(-2) η(176z)^5 η(352z)^(-2)` at level 352. -/
abbrev cuspForm_88_eta_1p1_4m1_8p2_11p1_22m2_44p5_88m2_old_352_4 : gamma0CuspForms 352 :=
  gamma0Rescale cuspForm_88_eta_1p1_4m1_8p2_11p1_22m2_44p5_88m2 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_88_eta_1p1_4m1_8p2_11p1_22m2_44p5_88m2_old_352_4_eq_eta :
    cuspForm_88_eta_1p1_4m1_8p2_11p1_22m2_44p5_88m2_old_352_4 =
      etaQuotientCuspForm 352 sparse![352; 3 => 1, 15 => -1, 31 => 2, 43 => 1, 87 => -2, 175 => 5, 351 => -2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_88_eta_1p1_4m1_8p2_11p1_22m2_44p5_88m2_old_352_4_first_coeffs :
    first_coeffs 100 cuspForm_88_eta_1p1_4m1_8p2_11p1_22m2_44p5_88m2_old_352_4 =
    [0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
     -1, 0, 0, 0, -2, 0, 0, 0, -1, 0, 0, 0, 2, 0, 0, 0, -1, 0, 0, 0,
     0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
