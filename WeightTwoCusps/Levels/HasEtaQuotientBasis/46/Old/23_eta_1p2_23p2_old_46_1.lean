module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«23».New.«23_eta_1p2_23p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 46

The eta expression is `η(z)^2 η(23z)^2`; see
[the local level table](../../TABLE.md#level-46).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_23_eta_1p2_23p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^2 η(23z)^2` at level 46. -/
abbrev cuspForm_23_eta_1p2_23p2_old_46_1 : gamma0CuspForms 46 :=
  gamma0RescaleToLevel cuspForm_23_eta_1p2_23p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_23_eta_1p2_23p2_old_46_1_eq_eta :
    cuspForm_23_eta_1p2_23p2_old_46_1 =
      etaQuotientCuspForm 46 sparse![46; 0 => 2, 22 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_23_eta_1p2_23p2_old_46_1_first_coeffs :
    first_coeffs 100 cuspForm_23_eta_1p2_23p2_old_46_1 =
    [0, 0, 1, -2, -1, 2, 1, 2, -2, 0, -2, -2, 1, 0, 0, 2, 3, -2, 2, 0,
     0, -2, -2, 0, 0, -4, 3, 2, -2, 0, -6, 6, 1, 6, 4, 0, -2, -2, -2, -6,
     2, -4, -4, 0, 4, 4, 1, -2, 3, 4, 3, -6, -3, 4, -1, -4, -2, 4, -3, 4,
     4, -8, -3, 4, -2, 6, 2, 2, -2, -2, 4, 2, -4, -4, 2, -2, 2, -8, 3, -8,
     -6, 0, 3, 2, 6, 8, 0, 6, 6, -4, -4, 6, -1, 0, 1, -4, -9, 6, -3, -4] := by
  eta_coeff

end WeightTwoCusps
