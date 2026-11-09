module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«189».New.«189_eta_1m1_3p3_7p1_21m1_63p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 378

The eta expression is `η(z)^(-1) η(3z)^3 η(7z) η(21z)^(-1) η(63z)^2`; see
[the local level table](../../TABLE.md#level-378).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_189_eta_1m1_3p3_7p1_21m1_63p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^3 η(7z) η(21z)^(-1) η(63z)^2` at level 378. -/
abbrev cuspForm_189_eta_1m1_3p3_7p1_21m1_63p2_old_378_1 : gamma0CuspForms 378 :=
  gamma0RescaleToLevel cuspForm_189_eta_1m1_3p3_7p1_21m1_63p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_189_eta_1m1_3p3_7p1_21m1_63p2_old_378_1_eq_eta :
    cuspForm_189_eta_1m1_3p3_7p1_21m1_63p2_old_378_1 =
      etaQuotientCuspForm 378 sparse![378; 0 => -1, 2 => 3, 6 => 1, 20 => -1, 62 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_189_eta_1m1_3p3_7p1_21m1_63p2_old_378_1_first_coeffs :
    first_coeffs 100 cuspForm_189_eta_1m1_3p3_7p1_21m1_63p2_old_378_1 =
    [0, 0, 0, 0, 0, 1, 1, 2, 0, 2, 1, 2, -1, 0, 0, 2, -2, 1, -2, 1,
     -2, -1, 0, -2, -3, 0, 0, 2, -3, -2, 4, 1, 0, -4, -2, 1, -2, -2, 0, -2,
     1, -1, -1, -2, -4, -4, 2, 3, 2, -1, 0, 6, 2, -2, -2, -1, 0, 4, -4, 3,
     -2, 2, 0, -2, 0, -4, -5, 2, -2, 0, 0, 0, 6, 0, 0, -4, -3, 2, -2, 0,
     4, 2, 1, 1, 0, -2, 0, 2, 2, 2, 4, 9, 4, 2, 2, 2, 5, 2, 0, 8] := by
  eta_coeff

end WeightTwoCusps
