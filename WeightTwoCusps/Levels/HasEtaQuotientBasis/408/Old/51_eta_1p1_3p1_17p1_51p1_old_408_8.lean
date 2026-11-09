module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«51».New.«51_eta_1p1_3p1_17p1_51p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 408

The eta expression is `η(8z) η(24z) η(136z) η(408z)`; see
[the local level table](../../TABLE.md#level-408).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(8z)` of `cuspForm_51_eta_1p1_3p1_17p1_51p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(8z) η(24z) η(136z) η(408z)` at level 408. -/
abbrev cuspForm_51_eta_1p1_3p1_17p1_51p1_old_408_8 : gamma0CuspForms 408 :=
  gamma0Rescale cuspForm_51_eta_1p1_3p1_17p1_51p1 8

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_51_eta_1p1_3p1_17p1_51p1_old_408_8_eq_eta :
    cuspForm_51_eta_1p1_3p1_17p1_51p1_old_408_8 =
      etaQuotientCuspForm 408 sparse![408; 7 => 1, 23 => 1, 135 => 1, 407 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_51_eta_1p1_3p1_17p1_51p1_old_408_8_first_coeffs :
    first_coeffs 100 cuspForm_51_eta_1p1_3p1_17p1_51p1_old_408_8 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0,
     -1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
     0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0,
     2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
