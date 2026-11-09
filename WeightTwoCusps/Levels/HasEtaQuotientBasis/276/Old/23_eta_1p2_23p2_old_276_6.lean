module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«23».New.«23_eta_1p2_23p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 276

The eta expression is `η(6z)^2 η(138z)^2`; see
[the local level table](../../TABLE.md#level-276).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(6z)` of `cuspForm_23_eta_1p2_23p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z)^2 η(138z)^2` at level 276. -/
abbrev cuspForm_23_eta_1p2_23p2_old_276_6 : gamma0CuspForms 276 :=
  gamma0RescaleToLevel cuspForm_23_eta_1p2_23p2 6 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_23_eta_1p2_23p2_old_276_6_eq_eta :
    cuspForm_23_eta_1p2_23p2_old_276_6 =
      etaQuotientCuspForm 276 sparse![276; 5 => 2, 137 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_23_eta_1p2_23p2_old_276_6_first_coeffs :
    first_coeffs 100 cuspForm_23_eta_1p2_23p2_old_276_6 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -2, 0,
     0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0,
     0, 0, 2, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     -2, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
