module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«126».New.«126_eta_3m1_6p1_9p4_18m2_21m1_42p1_63p4_126m2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 378

The eta expression is `η(3z)^(-1) η(6z) η(9z)^4 η(18z)^(-2) η(21z)^(-1) η(42z) η(63z)^4 η(126z)^(-2)`; see
[the local level table](../../TABLE.md#level-378).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_126_eta_3m1_6p1_9p4_18m2_21m1_42p1_63p4_126m2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-1) η(6z) η(9z)^4 η(18z)^(-2) η(21z)^(-1) η(42z) η(63z)^4 η(126z)^(-2)` at level 378. -/
abbrev cuspForm_126_eta_3m1_6p1_9p4_18m2_21m1_42p1_63p4_126m2_old_378_1 : gamma0CuspForms 378 :=
  gamma0RescaleToLevel cuspForm_126_eta_3m1_6p1_9p4_18m2_21m1_42p1_63p4_126m2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_126_eta_3m1_6p1_9p4_18m2_21m1_42p1_63p4_126m2_old_378_1_eq_eta :
    cuspForm_126_eta_3m1_6p1_9p4_18m2_21m1_42p1_63p4_126m2_old_378_1 =
      etaQuotientCuspForm 378 sparse![378; 2 => -1, 5 => 1, 8 => 4, 17 => -2, 20 => -1, 41 => 1, 62 => 4, 125 => -2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_126_eta_3m1_6p1_9p4_18m2_21m1_42p1_63p4_126m2_old_378_1_first_coeffs :
    first_coeffs 100 cuspForm_126_eta_3m1_6p1_9p4_18m2_21m1_42p1_63p4_126m2_old_378_1 =
    [0, 1, 0, 0, 1, 0, 0, 1, 0, 0, -2, 0, 0, -2, 0, 0, -1, 0, 0, 0,
     0, 0, 2, 0, 0, -1, 0, 0, 1, 0, 0, -4, 0, 0, -2, 0, 0, 2, 0, 0,
     2, 0, 0, 4, 0, 0, -2, 0, 0, 1, 0, 0, -2, 0, 0, -4, 0, 0, 4, 0,
     0, 2, 0, 0, 1, 0, 0, -4, 0, 0, -2, 0, 0, 6, 0, 0, 0, 0, 0, 8,
     0, 0, 2, 0, 0, -4, 0, 0, -2, 0, 0, -2, 0, 0, 12, 0, 0, -2, 0, 0] := by
  eta_coeff

end WeightTwoCusps
