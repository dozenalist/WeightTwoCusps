module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«126».New.«126_eta_1m2_2p3_3p3_6m2_9m1_14p1_18p1_21m1_42p2_63p1_126m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 378

The eta expression is `η(3z)^(-2) η(6z)^3 η(9z)^3 η(18z)^(-2) η(27z)^(-1) η(42z) η(54z) η(63z)^(-1) η(126z)^2 η(189z) η(378z)^(-1)`; see
[the local level table](../../TABLE.md#level-378).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_126_eta_1m2_2p3_3p3_6m2_9m1_14p1_18p1_21m1_42p2_63p1_126m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-2) η(6z)^3 η(9z)^3 η(18z)^(-2) η(27z)^(-1) η(42z) η(54z) η(63z)^(-1) η(126z)^2 η(189z) η(378z)^(-1)` at level 378. -/
abbrev cuspForm_126_eta_1m2_2p3_3p3_6m2_9m1_14p1_18p1_21m1_42p2_63p1_126m1_old_378_3 : gamma0CuspForms 378 :=
  gamma0Rescale cuspForm_126_eta_1m2_2p3_3p3_6m2_9m1_14p1_18p1_21m1_42p2_63p1_126m1 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_126_eta_1m2_2p3_3p3_6m2_9m1_14p1_18p1_21m1_42p2_63p1_126m1_old_378_3_eq_eta :
    cuspForm_126_eta_1m2_2p3_3p3_6m2_9m1_14p1_18p1_21m1_42p2_63p1_126m1_old_378_3 =
      etaQuotientCuspForm 378 sparse![378; 2 => -2, 5 => 3, 8 => 3, 17 => -2, 26 => -1, 41 => 1, 53 => 1, 62 => -1, 125 => 2, 188 => 1, 377 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_126_eta_1m2_2p3_3p3_6m2_9m1_14p1_18p1_21m1_42p2_63p1_126m1_old_378_3_first_coeffs :
    first_coeffs 100 cuspForm_126_eta_1m2_2p3_3p3_6m2_9m1_14p1_18p1_21m1_42p2_63p1_126m1_old_378_3 =
    [0, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0, 0, -1, 0, 0, 2,
     0, 0, 0, 0, 0, -3, 0, 0, -1, 0, 0, -4, 0, 0, -1, 0, 0, -2, 0, 0,
     -1, 0, 0, -1, 0, 0, -1, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, -1, 0,
     0, -1, 0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, -2, 0, 0, -4, 0, 0, 2] := by
  eta_coeff

end WeightTwoCusps
