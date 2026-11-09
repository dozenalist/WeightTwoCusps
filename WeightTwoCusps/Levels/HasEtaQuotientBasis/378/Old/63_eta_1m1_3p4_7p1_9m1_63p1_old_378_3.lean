module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«63».New.«63_eta_1m1_3p4_7p1_9m1_63p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 378

The eta expression is `η(3z)^(-1) η(9z)^4 η(21z) η(27z)^(-1) η(189z)`; see
[the local level table](../../TABLE.md#level-378).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-1) η(9z)^4 η(21z) η(27z)^(-1) η(189z)` at level 378. -/
abbrev cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1_old_378_3 : gamma0CuspForms 378 :=
  gamma0RescaleToLevel cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1 3 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1_old_378_3_eq_eta :
    cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1_old_378_3 =
      etaQuotientCuspForm 378 sparse![378; 2 => -1, 8 => 4, 20 => 1, 26 => -1, 188 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1_old_378_3_first_coeffs :
    first_coeffs 100 cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1_old_378_3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, -1, 0,
     0, 1, 0, 0, -1, 0, 0, 1, 0, 0, -4, 0, 0, -3, 0, 0, -1, 0, 0, 2,
     0, 0, -1, 0, 0, -2, 0, 0, -2, 0, 0, 2, 0, 0, -1, 0, 0, -4, 0, 0,
     0, 0, 0, -1, 0, 0, 5, 0, 0, 1, 0, 0, 3, 0, 0, 4, 0, 0, -2, 0,
     0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, -2, 0, 0, 4, 0, 0, 4] := by
  eta_coeff

end WeightTwoCusps
