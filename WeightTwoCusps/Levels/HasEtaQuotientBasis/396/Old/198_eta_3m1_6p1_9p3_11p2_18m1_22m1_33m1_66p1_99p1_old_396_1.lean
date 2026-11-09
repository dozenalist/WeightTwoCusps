module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«198».New.«198_eta_3m1_6p1_9p3_11p2_18m1_22m1_33m1_66p1_99p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 396

The eta expression is `η(3z)^(-1) η(6z) η(9z)^3 η(11z)^2 η(18z)^(-1) η(22z)^(-1) η(33z)^(-1) η(66z) η(99z)`; see
[the local level table](../../TABLE.md#level-396).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_198_eta_3m1_6p1_9p3_11p2_18m1_22m1_33m1_66p1_99p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-1) η(6z) η(9z)^3 η(11z)^2 η(18z)^(-1) η(22z)^(-1) η(33z)^(-1) η(66z) η(99z)` at level 396. -/
abbrev cuspForm_198_eta_3m1_6p1_9p3_11p2_18m1_22m1_33m1_66p1_99p1_old_396_1 : gamma0CuspForms 396 :=
  gamma0RescaleToLevel cuspForm_198_eta_3m1_6p1_9p3_11p2_18m1_22m1_33m1_66p1_99p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_198_eta_3m1_6p1_9p3_11p2_18m1_22m1_33m1_66p1_99p1_old_396_1_eq_eta :
    cuspForm_198_eta_3m1_6p1_9p3_11p2_18m1_22m1_33m1_66p1_99p1_old_396_1 =
      etaQuotientCuspForm 396 sparse![396; 2 => -1, 5 => 1, 8 => 3, 10 => 2, 17 => -1, 21 => -1, 32 => -1, 65 => 1, 98 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_198_eta_3m1_6p1_9p3_11p2_18m1_22m1_33m1_66p1_99p1_old_396_1_first_coeffs :
    first_coeffs 100 cuspForm_198_eta_3m1_6p1_9p3_11p2_18m1_22m1_33m1_66p1_99p1_old_396_1 =
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, -1, 0, -2, -1, 0,
     -2, 0, 0, -2, -1, 0, 2, 0, 0, 2, -2, 0, 0, 0, 0, 2, -1, 0, 0, 0,
     0, 4, 2, 0, 0, 0, 0, 2, -1, 0, 2, 0, 0, -2, 1, 0, 2, 0, 0, 0,
     -2, 0, -2, -2, 0, -2, 1, 0, -2, -1, 0, 4, 3, 0, 0, 3, 0, -2, 0, 0,
     0, -2, 0, -6, 2, 0, -2, 2, 0, 0, 0, 0, 2, -3, 0, -4, -1, 0, -2, 1] := by
  eta_coeff

end WeightTwoCusps
