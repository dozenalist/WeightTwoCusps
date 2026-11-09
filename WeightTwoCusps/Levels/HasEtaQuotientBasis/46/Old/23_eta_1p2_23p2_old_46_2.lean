module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«23».New.«23_eta_1p2_23p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 46

The eta expression is `η(2z)^2 η(46z)^2`; see
[the local level table](../../TABLE.md#level-46).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_23_eta_1p2_23p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^2 η(46z)^2` at level 46. -/
abbrev cuspForm_23_eta_1p2_23p2_old_46_2 : gamma0CuspForms 46 :=
  gamma0Rescale cuspForm_23_eta_1p2_23p2 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_23_eta_1p2_23p2_old_46_2_eq_eta :
    cuspForm_23_eta_1p2_23p2_old_46_2 =
      etaQuotientCuspForm 46 sparse![46; 1 => 2, 45 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_23_eta_1p2_23p2_old_46_2_first_coeffs :
    first_coeffs 100 cuspForm_23_eta_1p2_23p2_old_46_2 =
    [0, 0, 0, 0, 1, 0, -2, 0, -1, 0, 2, 0, 1, 0, 2, 0, -2, 0, 0, 0,
     -2, 0, -2, 0, 1, 0, 0, 0, 0, 0, 2, 0, 3, 0, -2, 0, 2, 0, 0, 0,
     0, 0, -2, 0, -2, 0, 0, 0, 0, 0, -4, 0, 3, 0, 2, 0, -2, 0, 0, 0,
     -6, 0, 6, 0, 1, 0, 6, 0, 4, 0, 0, 0, -2, 0, -2, 0, -2, 0, -6, 0,
     2, 0, -4, 0, -4, 0, 0, 0, 4, 0, 4, 0, 1, 0, -2, 0, 3, 0, 4, 0] := by
  eta_coeff

end WeightTwoCusps
