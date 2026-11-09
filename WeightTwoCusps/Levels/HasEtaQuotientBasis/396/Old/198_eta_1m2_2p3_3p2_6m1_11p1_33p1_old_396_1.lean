module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«198».New.«198_eta_1m2_2p3_3p2_6m1_11p1_33p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 396

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^2 η(6z)^(-1) η(11z) η(33z)`; see
[the local level table](../../TABLE.md#level-396).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_198_eta_1m2_2p3_3p2_6m1_11p1_33p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^2 η(6z)^(-1) η(11z) η(33z)` at level 396. -/
abbrev cuspForm_198_eta_1m2_2p3_3p2_6m1_11p1_33p1_old_396_1 : gamma0CuspForms 396 :=
  gamma0RescaleToLevel cuspForm_198_eta_1m2_2p3_3p2_6m1_11p1_33p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_198_eta_1m2_2p3_3p2_6m1_11p1_33p1_old_396_1_eq_eta :
    cuspForm_198_eta_1m2_2p3_3p2_6m1_11p1_33p1_old_396_1 =
      etaQuotientCuspForm 396 sparse![396; 0 => -2, 1 => 3, 2 => 2, 5 => -1, 10 => 1, 32 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_198_eta_1m2_2p3_3p2_6m1_11p1_33p1_old_396_1_first_coeffs :
    first_coeffs 100 cuspForm_198_eta_1m2_2p3_3p2_6m1_11p1_33p1_old_396_1 =
    [0, 0, 1, 2, 2, 2, 1, 2, 2, 2, 3, 0, 2, 1, 0, 0, -2, 3, 0, 0,
     0, -3, 1, 0, 1, -2, -4, 0, -3, -2, -1, -2, -1, -1, -2, -5, -6, -2, 0, -5,
     -4, -7, -4, -1, -1, -2, -7, 0, 0, -2, -6, -4, 1, -2, -1, -1, -4, 0, 4, 6,
     -2, 1, 5, 1, 2, 0, 1, -2, 5, 4, -4, -8, 8, 3, 1, 0, -9, 2, 0, 8,
     2, -2, 12, 3, 1, 2, 2, 14, -1, 8, -1, -6, 4, 4, 11, 3, -1, 6, 4, 2] := by
  eta_coeff

end WeightTwoCusps
