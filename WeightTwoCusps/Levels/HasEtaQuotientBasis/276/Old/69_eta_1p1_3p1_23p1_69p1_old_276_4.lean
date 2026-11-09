module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«69».New.«69_eta_1p1_3p1_23p1_69p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 276

The eta expression is `η(4z) η(12z) η(92z) η(276z)`; see
[the local level table](../../TABLE.md#level-276).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_69_eta_1p1_3p1_23p1_69p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z) η(12z) η(92z) η(276z)` at level 276. -/
abbrev cuspForm_69_eta_1p1_3p1_23p1_69p1_old_276_4 : gamma0CuspForms 276 :=
  gamma0Rescale cuspForm_69_eta_1p1_3p1_23p1_69p1 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_69_eta_1p1_3p1_23p1_69p1_old_276_4_eq_eta :
    cuspForm_69_eta_1p1_3p1_23p1_69p1_old_276_4 =
      etaQuotientCuspForm 276 sparse![276; 3 => 1, 11 => 1, 91 => 1, 275 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_69_eta_1p1_3p1_23p1_69p1_old_276_4_first_coeffs :
    first_coeffs 100 cuspForm_69_eta_1p1_3p1_23p1_69p1_old_276_4 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
     -1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0,
     -1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     -1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
     -1, 0, 0, 0, -1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
