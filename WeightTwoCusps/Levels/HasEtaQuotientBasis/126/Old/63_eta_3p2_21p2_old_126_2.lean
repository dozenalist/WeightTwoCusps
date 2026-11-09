module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«63».New.«63_eta_3p2_21p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 126

The eta expression is `η(6z)^2 η(42z)^2`; see
[the local level table](../../TABLE.md#level-126).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_63_eta_3p2_21p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z)^2 η(42z)^2` at level 126. -/
abbrev cuspForm_63_eta_3p2_21p2_old_126_2 : gamma0CuspForms 126 :=
  gamma0Rescale cuspForm_63_eta_3p2_21p2 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_63_eta_3p2_21p2_old_126_2_eq_eta :
    cuspForm_63_eta_3p2_21p2_old_126_2 =
      etaQuotientCuspForm 126 sparse![126; 5 => 2, 41 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_63_eta_3p2_21p2_old_126_2_first_coeffs :
    first_coeffs 100 cuspForm_63_eta_3p2_21p2_old_126_2 =
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0,
     -2, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, -3, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, -4, 0, 0, 0,
     0, 0, 6, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
