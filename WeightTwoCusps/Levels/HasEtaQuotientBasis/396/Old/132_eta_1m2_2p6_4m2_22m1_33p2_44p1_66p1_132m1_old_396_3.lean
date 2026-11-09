module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«132».New.«132_eta_1m2_2p6_4m2_22m1_33p2_44p1_66p1_132m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 396

The eta expression is `η(3z)^(-2) η(6z)^6 η(12z)^(-2) η(66z)^(-1) η(99z)^2 η(132z) η(198z) η(396z)^(-1)`; see
[the local level table](../../TABLE.md#level-396).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_132_eta_1m2_2p6_4m2_22m1_33p2_44p1_66p1_132m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-2) η(6z)^6 η(12z)^(-2) η(66z)^(-1) η(99z)^2 η(132z) η(198z) η(396z)^(-1)` at level 396. -/
abbrev cuspForm_132_eta_1m2_2p6_4m2_22m1_33p2_44p1_66p1_132m1_old_396_3 : gamma0CuspForms 396 :=
  gamma0Rescale cuspForm_132_eta_1m2_2p6_4m2_22m1_33p2_44p1_66p1_132m1 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_132_eta_1m2_2p6_4m2_22m1_33p2_44p1_66p1_132m1_old_396_3_eq_eta :
    cuspForm_132_eta_1m2_2p6_4m2_22m1_33p2_44p1_66p1_132m1_old_396_3 =
      etaQuotientCuspForm 396 sparse![396; 2 => -2, 5 => 6, 11 => -2, 65 => -1, 98 => 2, 131 => 1, 197 => 1, 395 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_132_eta_1m2_2p6_4m2_22m1_33p2_44p1_66p1_132m1_old_396_3_first_coeffs :
    first_coeffs 100 cuspForm_132_eta_1m2_2p6_4m2_22m1_33p2_44p1_66p1_132m1_old_396_3 =
    [0, 0, 0, 1, 0, 0, 2, 0, 0, -1, 0, 0, -2, 0, 0, 1, 0, 0, -2, 0,
     0, -2, 0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0,
     0, 0, -2, 0, 0, 3, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0,
     2, 0, 0, -2, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 0, -2, 0, 0, -2, 0,
     0, 3, 0, 0, -4, 0, 0, -4, 0, 0, -2, 0, 0, -1, 0, 0, 0, 0, 0, 1] := by
  eta_coeff

end WeightTwoCusps
