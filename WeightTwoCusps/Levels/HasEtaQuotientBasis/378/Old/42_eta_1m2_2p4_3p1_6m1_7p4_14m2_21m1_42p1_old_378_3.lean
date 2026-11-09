module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«42».New.«42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 378

The eta expression is `η(3z)^(-2) η(6z)^4 η(9z) η(18z)^(-1) η(21z)^4 η(42z)^(-2) η(63z)^(-1) η(126z)`; see
[the local level table](../../TABLE.md#level-378).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-2) η(6z)^4 η(9z) η(18z)^(-1) η(21z)^4 η(42z)^(-2) η(63z)^(-1) η(126z)` at level 378. -/
abbrev cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_378_3 : gamma0CuspForms 378 :=
  gamma0RescaleToLevel cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1 3 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_378_3_eq_eta :
    cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_378_3 =
      etaQuotientCuspForm 378 sparse![378; 2 => -2, 5 => 4, 8 => 1, 17 => -1, 20 => 4, 41 => -2, 62 => -1, 125 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_378_3_first_coeffs :
    first_coeffs 100 cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_378_3 =
    [0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0,
     0, 1, 0, 0, -4, 0, 0, -8, 0, 0, -6, 0, 0, -6, 0, 0, 1, 0, 0, 2,
     0, 0, -4, 0, 0, 3, 0, 0, 7, 0, 0, 12, 0, 0, 11, 0, 0, -4, 0, 0,
     0, 0, 0, 4, 0, 0, 6, 0, 0, 6, 0, 0, -7, 0, 0, -5, 0, 0, 4, 0,
     0, 7, 0, 0, 1, 0, 0, -6, 0, 0, -3, 0, 0, -4, 0, 0, 2, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
