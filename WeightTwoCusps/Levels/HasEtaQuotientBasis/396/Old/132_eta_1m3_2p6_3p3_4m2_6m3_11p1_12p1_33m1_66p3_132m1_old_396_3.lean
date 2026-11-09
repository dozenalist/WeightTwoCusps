module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«132».New.«132_eta_1m3_2p6_3p3_4m2_6m3_11p1_12p1_33m1_66p3_132m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 396

The eta expression is `η(3z)^(-3) η(6z)^6 η(9z)^3 η(12z)^(-2) η(18z)^(-3) η(33z) η(36z) η(99z)^(-1) η(198z)^3 η(396z)^(-1)`; see
[the local level table](../../TABLE.md#level-396).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_132_eta_1m3_2p6_3p3_4m2_6m3_11p1_12p1_33m1_66p3_132m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-3) η(6z)^6 η(9z)^3 η(12z)^(-2) η(18z)^(-3) η(33z) η(36z) η(99z)^(-1) η(198z)^3 η(396z)^(-1)` at level 396. -/
abbrev cuspForm_132_eta_1m3_2p6_3p3_4m2_6m3_11p1_12p1_33m1_66p3_132m1_old_396_3 : gamma0CuspForms 396 :=
  gamma0Rescale cuspForm_132_eta_1m3_2p6_3p3_4m2_6m3_11p1_12p1_33m1_66p3_132m1 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_132_eta_1m3_2p6_3p3_4m2_6m3_11p1_12p1_33m1_66p3_132m1_old_396_3_eq_eta :
    cuspForm_132_eta_1m3_2p6_3p3_4m2_6m3_11p1_12p1_33m1_66p3_132m1_old_396_3 =
      etaQuotientCuspForm 396 sparse![396; 2 => -3, 5 => 6, 8 => 3, 11 => -2, 17 => -3, 32 => 1, 35 => 1, 98 => -1, 197 => 3, 395 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_132_eta_1m3_2p6_3p3_4m2_6m3_11p1_12p1_33m1_66p3_132m1_old_396_3_first_coeffs :
    first_coeffs 100 cuspForm_132_eta_1m3_2p6_3p3_4m2_6m3_11p1_12p1_33m1_66p3_132m1_old_396_3 =
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 0, 0, 3, 0, 0, 1, 0, 0, -1, 0,
     0, 0, 0, 0, 3, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, -3, 0, 0, -2,
     0, 0, -4, 0, 0, 0, 0, 0, -1, 0, 0, -2, 0, 0, 1, 0, 0, -6, 0, 0,
     -2, 0, 0, -2, 0, 0, -1, 0, 0, 3, 0, 0, -3, 0, 0, -1, 0, 0, -6, 0,
     0, -4, 0, 0, 4, 0, 0, 0, 0, 0, -2, 0, 0, -5, 0, 0, -5, 0, 0, 1] := by
  eta_coeff

end WeightTwoCusps
