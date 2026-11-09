module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«88».New.«88_eta_1m2_2p4_4p1_8m1_11p2_22m2_44p3_88m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 352

The eta expression is `η(z)^(-2) η(2z)^4 η(4z) η(8z)^(-1) η(11z)^2 η(22z)^(-2) η(44z)^3 η(88z)^(-1)`; see
[the local level table](../../TABLE.md#level-352).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_88_eta_1m2_2p4_4p1_8m1_11p2_22m2_44p3_88m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(4z) η(8z)^(-1) η(11z)^2 η(22z)^(-2) η(44z)^3 η(88z)^(-1)` at level 352. -/
abbrev cuspForm_88_eta_1m2_2p4_4p1_8m1_11p2_22m2_44p3_88m1_old_352_1 : gamma0CuspForms 352 :=
  gamma0RescaleToLevel cuspForm_88_eta_1m2_2p4_4p1_8m1_11p2_22m2_44p3_88m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_88_eta_1m2_2p4_4p1_8m1_11p2_22m2_44p3_88m1_old_352_1_eq_eta :
    cuspForm_88_eta_1m2_2p4_4p1_8m1_11p2_22m2_44p3_88m1_old_352_1 =
      etaQuotientCuspForm 352 sparse![352; 0 => -2, 1 => 4, 3 => 1, 7 => -1, 10 => 2, 21 => -2, 43 => 3, 87 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_88_eta_1m2_2p4_4p1_8m1_11p2_22m2_44p3_88m1_old_352_1_first_coeffs :
    first_coeffs 100 cuspForm_88_eta_1m2_2p4_4p1_8m1_11p2_22m2_44p3_88m1_old_352_1 =
    [0, 1, 2, 1, 2, 1, -2, 2, 0, -2, 2, -1, -2, -4, -4, -7, -4, 6, -4, 0,
     2, -6, 2, 1, 0, 4, 8, 3, -4, 0, -2, 1, 8, -1, -4, 2, -4, -5, 0, 4,
     0, 0, 4, -10, 2, 6, -2, 8, 4, 5, -8, -2, 8, 2, 10, -1, 0, 8, 0, 3,
     -2, -4, 14, -4, -8, -4, -2, 7, -4, 1, -4, 3, 0, -4, 6, -4, 0, -2, -8, -6,
     -4, -7, -16, 6, 4, -10, -12, 0, 0, -9, -4, -16, -2, 1, 16, -16, -8, 9, -6, 2] := by
  eta_coeff

end WeightTwoCusps
