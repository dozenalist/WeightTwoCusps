module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«51».New.«51_eta_1p1_3p1_17p1_51p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 408

The eta expression is `η(z) η(3z) η(17z) η(51z)`; see
[the local level table](../../TABLE.md#level-408).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_51_eta_1p1_3p1_17p1_51p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(3z) η(17z) η(51z)` at level 408. -/
abbrev cuspForm_51_eta_1p1_3p1_17p1_51p1_old_408_1 : gamma0CuspForms 408 :=
  gamma0RescaleToLevel cuspForm_51_eta_1p1_3p1_17p1_51p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_51_eta_1p1_3p1_17p1_51p1_old_408_1_eq_eta :
    cuspForm_51_eta_1p1_3p1_17p1_51p1_old_408_1 =
      etaQuotientCuspForm 408 sparse![408; 0 => 1, 2 => 1, 16 => 1, 50 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_51_eta_1p1_3p1_17p1_51p1_old_408_1_first_coeffs :
    first_coeffs 100 cuspForm_51_eta_1p1_3p1_17p1_51p1_old_408_1 =
    [0, 0, 0, 1, -1, -1, -1, 1, 2, -1, 2, 0, 0, -1, -1, -1, -1, 0, 1, -1,
     -2, 3, 1, 2, 1, -1, 0, -2, -1, 2, 0, 1, 0, 0, 0, -2, 0, 0, -2, -1,
     2, -1, -3, 1, -1, 1, -1, 2, 0, 4, 4, 1, 0, 0, 2, -1, 3, -3, -6, -4,
     4, -4, 1, -3, 1, 1, -1, 0, -1, 2, 2, -1, -1, 0, -2, 0, 4, 0, 2, 3,
     -4, 2, 0, 0, -3, -1, 2, 4, 1, 2, 0, -2, 1, 3, -4, 5, -5, 2, -4, 0] := by
  eta_coeff

end WeightTwoCusps
