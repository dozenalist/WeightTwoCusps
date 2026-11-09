module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«63».New.«63_eta_1m1_3p4_7p1_9m1_63p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 378

The eta expression is `η(2z)^(-1) η(6z)^4 η(14z) η(18z)^(-1) η(126z)`; see
[the local level table](../../TABLE.md#level-378).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-1) η(6z)^4 η(14z) η(18z)^(-1) η(126z)` at level 378. -/
abbrev cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1_old_378_2 : gamma0CuspForms 378 :=
  gamma0RescaleToLevel cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1_old_378_2_eq_eta :
    cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1_old_378_2 =
      etaQuotientCuspForm 378 sparse![378; 1 => -1, 5 => 4, 13 => 1, 17 => -1, 125 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1_old_378_2_first_coeffs :
    first_coeffs 100 cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1_old_378_2 =
    [0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 2, 0, -1, 0, 1, 0, -1, 0, 1, 0,
     -4, 0, -3, 0, -1, 0, 2, 0, -1, 0, -2, 0, -2, 0, 2, 0, -1, 0, -4, 0,
     0, 0, -1, 0, 5, 0, 1, 0, 3, 0, 4, 0, -2, 0, 1, 0, 0, 0, 1, 0,
     2, 0, -2, 0, 4, 0, 4, 0, 0, 0, 0, 0, -1, 0, -2, 0, 4, 0, -2, 0,
     6, 0, -4, 0, 1, 0, 0, 0, 1, 0, -2, 0, -3, 0, -2, 0, -1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
