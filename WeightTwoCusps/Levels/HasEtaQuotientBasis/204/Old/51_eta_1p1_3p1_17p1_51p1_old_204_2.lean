module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«51».New.«51_eta_1p1_3p1_17p1_51p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 204

The eta expression is `η(2z) η(6z) η(34z) η(102z)`; see
[the local level table](../../TABLE.md#level-204).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_51_eta_1p1_3p1_17p1_51p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(6z) η(34z) η(102z)` at level 204. -/
abbrev cuspForm_51_eta_1p1_3p1_17p1_51p1_old_204_2 : gamma0CuspForms 204 :=
  gamma0RescaleToLevel cuspForm_51_eta_1p1_3p1_17p1_51p1 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_51_eta_1p1_3p1_17p1_51p1_old_204_2_eq_eta :
    cuspForm_51_eta_1p1_3p1_17p1_51p1_old_204_2 =
      etaQuotientCuspForm 204 sparse![204; 1 => 1, 5 => 1, 33 => 1, 101 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_51_eta_1p1_3p1_17p1_51p1_old_204_2_first_coeffs :
    first_coeffs 100 cuspForm_51_eta_1p1_3p1_17p1_51p1_old_204_2 =
    [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, -1, 0, -1, 0, 1, 0, 2, 0, -1, 0,
     2, 0, 0, 0, 0, 0, -1, 0, -1, 0, -1, 0, -1, 0, 0, 0, 1, 0, -1, 0,
     -2, 0, 3, 0, 1, 0, 2, 0, 1, 0, -1, 0, 0, 0, -2, 0, -1, 0, 2, 0,
     0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, -2, 0, -1, 0,
     2, 0, -1, 0, -3, 0, 1, 0, -1, 0, 1, 0, -1, 0, 2, 0, 0, 0, 4, 0] := by
  eta_coeff

end WeightTwoCusps
