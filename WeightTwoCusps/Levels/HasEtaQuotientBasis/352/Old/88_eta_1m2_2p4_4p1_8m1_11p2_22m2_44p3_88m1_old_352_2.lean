module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«88».New.«88_eta_1m2_2p4_4p1_8m1_11p2_22m2_44p3_88m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 352

The eta expression is `η(2z)^(-2) η(4z)^4 η(8z) η(16z)^(-1) η(22z)^2 η(44z)^(-2) η(88z)^3 η(176z)^(-1)`; see
[the local level table](../../TABLE.md#level-352).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_88_eta_1m2_2p4_4p1_8m1_11p2_22m2_44p3_88m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-2) η(4z)^4 η(8z) η(16z)^(-1) η(22z)^2 η(44z)^(-2) η(88z)^3 η(176z)^(-1)` at level 352. -/
abbrev cuspForm_88_eta_1m2_2p4_4p1_8m1_11p2_22m2_44p3_88m1_old_352_2 : gamma0CuspForms 352 :=
  gamma0RescaleToLevel cuspForm_88_eta_1m2_2p4_4p1_8m1_11p2_22m2_44p3_88m1 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_88_eta_1m2_2p4_4p1_8m1_11p2_22m2_44p3_88m1_old_352_2_eq_eta :
    cuspForm_88_eta_1m2_2p4_4p1_8m1_11p2_22m2_44p3_88m1_old_352_2 =
      etaQuotientCuspForm 352 sparse![352; 1 => -2, 3 => 4, 7 => 1, 15 => -1, 21 => 2, 43 => -2, 87 => 3, 175 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_88_eta_1m2_2p4_4p1_8m1_11p2_22m2_44p3_88m1_old_352_2_first_coeffs :
    first_coeffs 100 cuspForm_88_eta_1m2_2p4_4p1_8m1_11p2_22m2_44p3_88m1_old_352_2 =
    [0, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, -2, 0, 2, 0, 0, 0, -2, 0,
     2, 0, -1, 0, -2, 0, -4, 0, -4, 0, -7, 0, -4, 0, 6, 0, -4, 0, 0, 0,
     2, 0, -6, 0, 2, 0, 1, 0, 0, 0, 4, 0, 8, 0, 3, 0, -4, 0, 0, 0,
     -2, 0, 1, 0, 8, 0, -1, 0, -4, 0, 2, 0, -4, 0, -5, 0, 0, 0, 4, 0,
     0, 0, 0, 0, 4, 0, -10, 0, 2, 0, 6, 0, -2, 0, 8, 0, 4, 0, 5, 0] := by
  eta_coeff

end WeightTwoCusps
