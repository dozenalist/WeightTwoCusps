module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«27».New.«27_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 378

The eta expression is `η(21z)^2 η(63z)^2`; see
[the local level table](../../TABLE.md#level-378).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(7z)` of `cuspForm_27_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(21z)^2 η(63z)^2` at level 378. -/
abbrev cuspForm_27_2_a_a_old_378_7 : gamma0CuspForms 378 :=
  gamma0RescaleToLevel cuspForm_27_2_a_a 7 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_27_2_a_a_old_378_7_eq_eta :
    cuspForm_27_2_a_a_old_378_7 =
      etaQuotientCuspForm 378 sparse![378; 20 => 2, 62 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_27_2_a_a_old_378_7_first_coeffs :
    first_coeffs 100 cuspForm_27_2_a_a_old_378_7 =
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
