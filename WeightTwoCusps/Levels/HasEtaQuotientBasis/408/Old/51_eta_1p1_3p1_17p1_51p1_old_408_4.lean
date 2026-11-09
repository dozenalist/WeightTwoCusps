module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«51».New.«51_eta_1p1_3p1_17p1_51p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 408

The eta expression is `η(4z) η(12z) η(68z) η(204z)`; see
[the local level table](../../TABLE.md#level-408).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_51_eta_1p1_3p1_17p1_51p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z) η(12z) η(68z) η(204z)` at level 408. -/
abbrev cuspForm_51_eta_1p1_3p1_17p1_51p1_old_408_4 : gamma0CuspForms 408 :=
  gamma0RescaleToLevel cuspForm_51_eta_1p1_3p1_17p1_51p1 4 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_51_eta_1p1_3p1_17p1_51p1_old_408_4_eq_eta :
    cuspForm_51_eta_1p1_3p1_17p1_51p1_old_408_4 =
      etaQuotientCuspForm 408 sparse![408; 3 => 1, 11 => 1, 67 => 1, 203 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_51_eta_1p1_3p1_17p1_51p1_old_408_4_first_coeffs :
    first_coeffs 100 cuspForm_51_eta_1p1_3p1_17p1_51p1_old_408_4 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0,
     -1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, -1, 0, 0, 0,
     2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0,
     -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0,
     -2, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
