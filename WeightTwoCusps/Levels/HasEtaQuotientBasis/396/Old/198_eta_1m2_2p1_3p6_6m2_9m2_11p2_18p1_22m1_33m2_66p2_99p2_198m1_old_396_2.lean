module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«198».New.«198_eta_1m2_2p1_3p6_6m2_9m2_11p2_18p1_22m1_33m2_66p2_99p2_198m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 396

The eta expression is `η(2z)^(-2) η(4z) η(6z)^6 η(12z)^(-2) η(18z)^(-2) η(22z)^2 η(36z) η(44z)^(-1) η(66z)^(-2) η(132z)^2 η(198z)^2 η(396z)^(-1)`; see
[the local level table](../../TABLE.md#level-396).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_198_eta_1m2_2p1_3p6_6m2_9m2_11p2_18p1_22m1_33m2_66p2_99p2_198m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-2) η(4z) η(6z)^6 η(12z)^(-2) η(18z)^(-2) η(22z)^2 η(36z) η(44z)^(-1) η(66z)^(-2) η(132z)^2 η(198z)^2 η(396z)^(-1)` at level 396. -/
abbrev cuspForm_198_eta_1m2_2p1_3p6_6m2_9m2_11p2_18p1_22m1_33m2_66p2_99p2_198m1_old_396_2 : gamma0CuspForms 396 :=
  gamma0Rescale cuspForm_198_eta_1m2_2p1_3p6_6m2_9m2_11p2_18p1_22m1_33m2_66p2_99p2_198m1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_198_eta_1m2_2p1_3p6_6m2_9m2_11p2_18p1_22m1_33m2_66p2_99p2_198m1_old_396_2_eq_eta :
    cuspForm_198_eta_1m2_2p1_3p6_6m2_9m2_11p2_18p1_22m1_33m2_66p2_99p2_198m1_old_396_2 =
      etaQuotientCuspForm 396 sparse![396; 1 => -2, 3 => 1, 5 => 6, 11 => -2, 17 => -2, 21 => 2, 35 => 1, 43 => -1, 65 => -2, 131 => 2, 197 => 2, 395 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_198_eta_1m2_2p1_3p6_6m2_9m2_11p2_18p1_22m1_33m2_66p2_99p2_198m1_old_396_2_first_coeffs :
    first_coeffs 100 cuspForm_198_eta_1m2_2p1_3p6_6m2_9m2_11p2_18p1_22m1_33m2_66p2_99p2_198m1_old_396_2 =
    [0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 4, 0, 2, 0, 2, 0, 0, 0, 3, 0,
     2, 0, 0, 0, 2, 0, 2, 0, 6, 0, -3, 0, -6, 0, -4, 0, -2, 0, 4, 0,
     -6, 0, -2, 0, 0, 0, 0, 0, 0, 0, -14, 0, -2, 0, -2, 0, 2, 0, -4, 0,
     -6, 0, 2, 0, 4, 0, 1, 0, -4, 0, -8, 0, -2, 0, 6, 0, 4, 0, 4, 0,
     6, 0, 4, 0, 4, 0, -12, 0, -2, 0, -1, 0, 6, 0, 14, 0, -4, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
