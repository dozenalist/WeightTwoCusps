module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«63».New.«63_eta_1m1_3p4_7p1_9m1_63p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 378

The eta expression is `η(z)^(-1) η(3z)^4 η(7z) η(9z)^(-1) η(63z)`; see
[the local level table](../../TABLE.md#level-378).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^4 η(7z) η(9z)^(-1) η(63z)` at level 378. -/
abbrev cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1_old_378_1 : gamma0CuspForms 378 :=
  gamma0RescaleToLevel cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1_old_378_1_eq_eta :
    cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1_old_378_1 =
      etaQuotientCuspForm 378 sparse![378; 0 => -1, 2 => 4, 6 => 1, 8 => -1, 62 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1_old_378_1_first_coeffs :
    first_coeffs 100 cuspForm_63_eta_1m1_3p4_7p1_9m1_63p1_old_378_1 =
    [0, 0, 0, 1, 1, 2, -1, 1, -1, 1, -4, -3, -1, 2, -1, -2, -2, 2, -1, -4,
     0, -1, 5, 1, 3, 4, -2, 1, 0, 1, 2, -2, 4, 4, 0, 0, -1, -2, 4, -2,
     6, -4, 1, 0, 1, -2, -3, -2, -1, 0, -4, -6, 0, -1, -1, -2, 2, 4, -1, -4,
     2, -4, 2, -1, -3, 0, -4, -4, -4, 0, -2, 3, 3, 10, 2, -1, 0, 1, 2, 12,
     -6, 1, 10, 6, 1, -12, 0, -2, -9, 8, 2, 0, 1, 0, 6, 0, -5, -2, 0, 4] := by
  eta_coeff

end WeightTwoCusps
