module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«20».New.«20_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 440

The eta expression is `η(4z)^2 η(20z)^2`; see
[the local level table](../../TABLE.md#level-440).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_20_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^2 η(20z)^2` at level 440. -/
abbrev cuspForm_20_2_a_a_old_440_2 : gamma0CuspForms 440 :=
  gamma0RescaleToLevel cuspForm_20_2_a_a 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_20_2_a_a_old_440_2_eq_eta :
    cuspForm_20_2_a_a_old_440_2 =
      etaQuotientCuspForm 440 sparse![440; 3 => 2, 19 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_20_2_a_a_old_440_2_first_coeffs :
    first_coeffs 100 cuspForm_20_2_a_a_old_440_2 =
    [0, 0, 1, 0, 0, 0, -2, 0, 0, 0, -1, 0, 0, 0, 2, 0, 0, 0, 1, 0,
     0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, -6, 0, 0, 0, -4, 0,
     0, 0, -4, 0, 0, 0, 6, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 6, 0,
     0, 0, -4, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 2, 0, 0, 0, -4, 0,
     0, 0, 6, 0, 0, 0, -10, 0, 0, 0, -1, 0, 0, 0, -6, 0, 0, 0, -3, 0] := by
  eta_coeff

end WeightTwoCusps
