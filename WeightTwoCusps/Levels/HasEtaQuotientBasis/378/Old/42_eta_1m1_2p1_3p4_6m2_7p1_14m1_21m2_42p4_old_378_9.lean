module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«42».New.«42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 378

The eta expression is `η(9z)^(-1) η(18z) η(27z)^4 η(54z)^(-2) η(63z) η(126z)^(-1) η(189z)^(-2) η(378z)^4`; see
[the local level table](../../TABLE.md#level-378).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(9z)` of `cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(9z)^(-1) η(18z) η(27z)^4 η(54z)^(-2) η(63z) η(126z)^(-1) η(189z)^(-2) η(378z)^4` at level 378. -/
abbrev cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_378_9 : gamma0CuspForms 378 :=
  gamma0Rescale cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4 9

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_378_9_eq_eta :
    cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_378_9 =
      etaQuotientCuspForm 378 sparse![378; 8 => -1, 17 => 1, 26 => 4, 53 => -2, 62 => 1, 125 => -1, 188 => -2, 377 => 4] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_378_9_first_coeffs :
    first_coeffs 100 cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_378_9 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
     0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0,
     0, -2, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
