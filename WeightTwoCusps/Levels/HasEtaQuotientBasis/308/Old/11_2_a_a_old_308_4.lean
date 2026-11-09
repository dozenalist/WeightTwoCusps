module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«11».New.«11_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 308

The eta expression is `η(4z)^2 η(44z)^2`; see
[the local level table](../../TABLE.md#level-308).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_11_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^2 η(44z)^2` at level 308. -/
abbrev cuspForm_11_2_a_a_old_308_4 : gamma0CuspForms 308 :=
  gamma0RescaleToLevel cuspForm_11_2_a_a 4 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_11_2_a_a_old_308_4_eq_eta :
    cuspForm_11_2_a_a_old_308_4 =
      etaQuotientCuspForm 308 sparse![308; 3 => 2, 43 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_11_2_a_a_old_308_4_first_coeffs :
    first_coeffs 100 cuspForm_11_2_a_a_old_308_4 =
    [0, 0, 0, 0, 1, 0, 0, 0, -2, 0, 0, 0, -1, 0, 0, 0, 2, 0, 0, 0,
     1, 0, 0, 0, 2, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0,
     -2, 0, 0, 0, 1, 0, 0, 0, -2, 0, 0, 0, 4, 0, 0, 0, 4, 0, 0, 0,
     -1, 0, 0, 0, -4, 0, 0, 0, -2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0,
     2, 0, 0, 0, 2, 0, 0, 0, -2, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
