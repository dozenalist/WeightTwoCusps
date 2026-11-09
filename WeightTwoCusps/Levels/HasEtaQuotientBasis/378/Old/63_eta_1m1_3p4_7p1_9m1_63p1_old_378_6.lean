module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«63».New.«63_eta_1m1_3p4_7p1_9m1_63p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 378

The eta expression is `η(6z)^(-1) η(18z)^4 η(42z) η(54z)^(-1) η(378z)`; see
[the local level table](../../TABLE.md#level-378).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(6z)` of `cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z)^(-1) η(18z)^4 η(42z) η(54z)^(-1) η(378z)` at level 378. -/
abbrev cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1_old_378_6 : gamma0CuspForms 378 :=
  gamma0Rescale cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1 6

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1_old_378_6_eq_eta :
    cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1_old_378_6 =
      etaQuotientCuspForm 378 sparse![378; 5 => -1, 17 => 4, 41 => 1, 53 => -1, 377 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1_old_378_6_first_coeffs :
    first_coeffs 100 cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1_old_378_6 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
     -4, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 2, 0,
     0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, -2, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
