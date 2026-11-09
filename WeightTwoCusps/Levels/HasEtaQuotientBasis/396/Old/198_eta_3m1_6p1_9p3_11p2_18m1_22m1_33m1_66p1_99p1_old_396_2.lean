module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«198».New.«198_eta_3m1_6p1_9p3_11p2_18m1_22m1_33m1_66p1_99p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 396

The eta expression is `η(6z)^(-1) η(12z) η(18z)^3 η(22z)^2 η(36z)^(-1) η(44z)^(-1) η(66z)^(-1) η(132z) η(198z)`; see
[the local level table](../../TABLE.md#level-396).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_198_eta_3m1_6p1_9p3_11p2_18m1_22m1_33m1_66p1_99p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z)^(-1) η(12z) η(18z)^3 η(22z)^2 η(36z)^(-1) η(44z)^(-1) η(66z)^(-1) η(132z) η(198z)` at level 396. -/
abbrev cuspForm_198_eta_3m1_6p1_9p3_11p2_18m1_22m1_33m1_66p1_99p1_old_396_2 : gamma0CuspForms 396 :=
  gamma0Rescale cuspForm_198_eta_3m1_6p1_9p3_11p2_18m1_22m1_33m1_66p1_99p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_198_eta_3m1_6p1_9p3_11p2_18m1_22m1_33m1_66p1_99p1_old_396_2_eq_eta :
    cuspForm_198_eta_3m1_6p1_9p3_11p2_18m1_22m1_33m1_66p1_99p1_old_396_2 =
      etaQuotientCuspForm 396 sparse![396; 5 => -1, 11 => 1, 17 => 3, 21 => 2, 35 => -1, 43 => -1, 65 => -1, 131 => 1, 197 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_198_eta_3m1_6p1_9p3_11p2_18m1_22m1_33m1_66p1_99p1_old_396_2_first_coeffs :
    first_coeffs 100 cuspForm_198_eta_3m1_6p1_9p3_11p2_18m1_22m1_33m1_66p1_99p1_old_396_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, -2, 0, -1, 0, 0, 0,
     -2, 0, 0, 0, 0, 0, -2, 0, -1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0,
     -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, -1, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, -1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
