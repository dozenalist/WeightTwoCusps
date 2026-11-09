module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«23».New.«23_eta_1p2_23p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 276

The eta expression is `η(12z)^2 η(276z)^2`; see
[the local level table](../../TABLE.md#level-276).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(12z)` of `cuspForm_23_eta_1p2_23p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(12z)^2 η(276z)^2` at level 276. -/
abbrev cuspForm_23_eta_1p2_23p2_old_276_12 : gamma0CuspForms 276 :=
  gamma0Rescale cuspForm_23_eta_1p2_23p2 12

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_23_eta_1p2_23p2_old_276_12_eq_eta :
    cuspForm_23_eta_1p2_23p2_old_276_12 =
      etaQuotientCuspForm 276 sparse![276; 11 => 2, 275 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_23_eta_1p2_23p2_old_276_12_first_coeffs :
    first_coeffs 100 cuspForm_23_eta_1p2_23p2_old_276_12 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
