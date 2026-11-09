module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«126».New.«126_eta_3m1_6p1_9p4_18m2_21m1_42p1_63p4_126m2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 378

The eta expression is `η(9z)^(-1) η(18z) η(27z)^4 η(54z)^(-2) η(63z)^(-1) η(126z) η(189z)^4 η(378z)^(-2)`; see
[the local level table](../../TABLE.md#level-378).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_126_eta_3m1_6p1_9p4_18m2_21m1_42p1_63p4_126m2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(9z)^(-1) η(18z) η(27z)^4 η(54z)^(-2) η(63z)^(-1) η(126z) η(189z)^4 η(378z)^(-2)` at level 378. -/
abbrev cuspForm_126_eta_3m1_6p1_9p4_18m2_21m1_42p1_63p4_126m2_old_378_3 : gamma0CuspForms 378 :=
  gamma0Rescale cuspForm_126_eta_3m1_6p1_9p4_18m2_21m1_42p1_63p4_126m2 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_126_eta_3m1_6p1_9p4_18m2_21m1_42p1_63p4_126m2_old_378_3_eq_eta :
    cuspForm_126_eta_3m1_6p1_9p4_18m2_21m1_42p1_63p4_126m2_old_378_3 =
      etaQuotientCuspForm 378 sparse![378; 8 => -1, 17 => 1, 26 => 4, 53 => -2, 62 => -1, 125 => 1, 188 => 4, 377 => -2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_126_eta_3m1_6p1_9p4_18m2_21m1_42p1_63p4_126m2_old_378_3_first_coeffs :
    first_coeffs 100 cuspForm_126_eta_3m1_6p1_9p4_18m2_21m1_42p1_63p4_126m2_old_378_3 =
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
     0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, -2,
     0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
