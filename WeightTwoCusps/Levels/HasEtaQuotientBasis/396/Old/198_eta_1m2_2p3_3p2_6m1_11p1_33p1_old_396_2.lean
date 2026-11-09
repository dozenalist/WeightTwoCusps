module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«198».New.«198_eta_1m2_2p3_3p2_6m1_11p1_33p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 396

The eta expression is `η(2z)^(-2) η(4z)^3 η(6z)^2 η(12z)^(-1) η(22z) η(66z)`; see
[the local level table](../../TABLE.md#level-396).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_198_eta_1m2_2p3_3p2_6m1_11p1_33p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-2) η(4z)^3 η(6z)^2 η(12z)^(-1) η(22z) η(66z)` at level 396. -/
abbrev cuspForm_198_eta_1m2_2p3_3p2_6m1_11p1_33p1_old_396_2 : gamma0CuspForms 396 :=
  gamma0Rescale cuspForm_198_eta_1m2_2p3_3p2_6m1_11p1_33p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_198_eta_1m2_2p3_3p2_6m1_11p1_33p1_old_396_2_eq_eta :
    cuspForm_198_eta_1m2_2p3_3p2_6m1_11p1_33p1_old_396_2 =
      etaQuotientCuspForm 396 sparse![396; 1 => -2, 3 => 3, 5 => 2, 11 => -1, 21 => 1, 65 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_198_eta_1m2_2p3_3p2_6m1_11p1_33p1_old_396_2_first_coeffs :
    first_coeffs 100 cuspForm_198_eta_1m2_2p3_3p2_6m1_11p1_33p1_old_396_2 =
    [0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0,
     3, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, -2, 0, 3, 0, 0, 0, 0, 0,
     0, 0, -3, 0, 1, 0, 0, 0, 1, 0, -2, 0, -4, 0, 0, 0, -3, 0, -2, 0,
     -1, 0, -2, 0, -1, 0, -1, 0, -2, 0, -5, 0, -6, 0, -2, 0, 0, 0, -5, 0,
     -4, 0, -7, 0, -4, 0, -1, 0, -1, 0, -2, 0, -7, 0, 0, 0, 0, 0, -2, 0] := by
  eta_coeff

end WeightTwoCusps
