module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«126».New.«126_eta_1m2_2p3_3p3_6m2_9m1_14p1_18p1_21m1_42p2_63p1_126m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 378

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^3 η(6z)^(-2) η(9z)^(-1) η(14z) η(18z) η(21z)^(-1) η(42z)^2 η(63z) η(126z)^(-1)`; see
[the local level table](../../TABLE.md#level-378).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_126_eta_1m2_2p3_3p3_6m2_9m1_14p1_18p1_21m1_42p2_63p1_126m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^3 η(6z)^(-2) η(9z)^(-1) η(14z) η(18z) η(21z)^(-1) η(42z)^2 η(63z) η(126z)^(-1)` at level 378. -/
abbrev cuspForm_126_eta_1m2_2p3_3p3_6m2_9m1_14p1_18p1_21m1_42p2_63p1_126m1_old_378_1 : gamma0CuspForms 378 :=
  gamma0RescaleToLevel cuspForm_126_eta_1m2_2p3_3p3_6m2_9m1_14p1_18p1_21m1_42p2_63p1_126m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_126_eta_1m2_2p3_3p3_6m2_9m1_14p1_18p1_21m1_42p2_63p1_126m1_old_378_1_eq_eta :
    cuspForm_126_eta_1m2_2p3_3p3_6m2_9m1_14p1_18p1_21m1_42p2_63p1_126m1_old_378_1 =
      etaQuotientCuspForm 378 sparse![378; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 8 => -1, 13 => 1, 17 => 1, 20 => -1, 41 => 2, 62 => 1, 125 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_126_eta_1m2_2p3_3p3_6m2_9m1_14p1_18p1_21m1_42p2_63p1_126m1_old_378_1_first_coeffs :
    first_coeffs 100 cuspForm_126_eta_1m2_2p3_3p3_6m2_9m1_14p1_18p1_21m1_42p2_63p1_126m1_old_378_1 =
    [0, 1, 2, 2, 1, -1, 0, 0, 1, 1, -2, 0, -1, 2, 0, -3, -1, -4, -1, -2,
     -1, -1, -1, 2, 2, 0, -1, -1, 0, 2, -1, -2, -4, 2, 2, 1, -2, -3, 1, -1,
     0, -4, -1, -1, -3, -1, 2, 6, 3, 1, 0, -2, 2, 0, 3, 0, 1, 3, 1, 7,
     3, 2, -4, 0, 2, -2, -2, 0, 8, 4, -1, 2, 1, 8, 4, -4, -2, 0, 5, 3,
     -3, 4, 0, -1, 2, -4, -2, -6, -2, -2, 1, -3, -1, -2, 6, 0, -6, -4, 2, 6] := by
  eta_coeff

end WeightTwoCusps
