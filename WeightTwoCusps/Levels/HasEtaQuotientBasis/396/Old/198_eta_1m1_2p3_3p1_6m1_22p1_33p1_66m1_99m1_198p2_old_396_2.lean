module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«198».New.«198_eta_1m1_2p3_3p1_6m1_22p1_33p1_66m1_99m1_198p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 396

The eta expression is `η(2z)^(-1) η(4z)^3 η(6z) η(12z)^(-1) η(44z) η(66z) η(132z)^(-1) η(198z)^(-1) η(396z)^2`; see
[the local level table](../../TABLE.md#level-396).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_198_eta_1m1_2p3_3p1_6m1_22p1_33p1_66m1_99m1_198p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-1) η(4z)^3 η(6z) η(12z)^(-1) η(44z) η(66z) η(132z)^(-1) η(198z)^(-1) η(396z)^2` at level 396. -/
abbrev cuspForm_198_eta_1m1_2p3_3p1_6m1_22p1_33p1_66m1_99m1_198p2_old_396_2 : gamma0CuspForms 396 :=
  gamma0Rescale cuspForm_198_eta_1m1_2p3_3p1_6m1_22p1_33p1_66m1_99m1_198p2 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_198_eta_1m1_2p3_3p1_6m1_22p1_33p1_66m1_99m1_198p2_old_396_2_eq_eta :
    cuspForm_198_eta_1m1_2p3_3p1_6m1_22p1_33p1_66m1_99m1_198p2_old_396_2 =
      etaQuotientCuspForm 396 sparse![396; 1 => -1, 3 => 3, 5 => 1, 11 => -1, 43 => 1, 65 => 1, 131 => -1, 197 => -1, 395 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_198_eta_1m1_2p3_3p1_6m1_22p1_33p1_66m1_99m1_198p2_old_396_2_first_coeffs :
    first_coeffs 100 cuspForm_198_eta_1m1_2p3_3p1_6m1_22p1_33p1_66m1_99m1_198p2_old_396_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1, 0, -2, 0, -1, 0, 1, 0, 0, 0,
     1, 0, -2, 0, 1, 0, 3, 0, 0, 0, 2, 0, 0, 0, 1, 0, -1, 0, 0, 0,
     0, 0, -2, 0, 1, 0, 0, 0, -1, 0, -3, 0, 0, 0, 1, 0, 1, 0, 0, 0,
     0, 0, -1, 0, -3, 0, 1, 0, -1, 0, -2, 0, 0, 0, 0, 0, 3, 0, 1, 0] := by
  eta_coeff

end WeightTwoCusps
