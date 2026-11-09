module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«11».New.«11_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 110

The eta expression is `η(5z)^2 η(55z)^2`; see
[the local level table](../../TABLE.md#level-110).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(5z)` of `cuspForm_11_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(5z)^2 η(55z)^2` at level 110. -/
abbrev cuspForm_11_2_a_a_old_110_5 : gamma0CuspForms 110 :=
  gamma0RescaleToLevel cuspForm_11_2_a_a 5 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_11_2_a_a_old_110_5_eq_eta :
    cuspForm_11_2_a_a_old_110_5 =
      etaQuotientCuspForm 110 sparse![110; 4 => 2, 54 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_11_2_a_a_old_110_5_first_coeffs :
    first_coeffs 100 cuspForm_11_2_a_a_old_110_5 =
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -2, 0, 0, 0, 0, -1, 0, 0, 0, 0,
     2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, -2, 0, 0, 0, 0,
     0, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 1, 0, 0, 0, 0,
     -2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 4, 0, 0, 0, 0, -1, 0, 0, 0, 0,
     -4, 0, 0, 0, 0, -2, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
