module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«11».New.«11_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 440

The eta expression is `η(8z)^2 η(88z)^2`; see
[the local level table](../../TABLE.md#level-440).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(8z)` of `cuspForm_11_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(8z)^2 η(88z)^2` at level 440. -/
abbrev cuspForm_11_2_a_a_old_440_8 : gamma0CuspForms 440 :=
  gamma0RescaleToLevel cuspForm_11_2_a_a 8 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_11_2_a_a_old_440_8_eq_eta :
    cuspForm_11_2_a_a_old_440_8 =
      etaQuotientCuspForm 440 sparse![440; 7 => 2, 87 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_11_2_a_a_old_440_8_first_coeffs :
    first_coeffs 100 cuspForm_11_2_a_a_old_440_8 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0,
     0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0,
     -2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
