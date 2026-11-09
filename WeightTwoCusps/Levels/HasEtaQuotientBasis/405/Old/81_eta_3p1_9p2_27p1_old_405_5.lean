module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«81».New.«81_eta_3p1_9p2_27p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 405

The eta expression is `η(15z) η(45z)^2 η(135z)`; see
[the local level table](../../TABLE.md#level-405).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(5z)` of `cuspForm_81_eta_3p1_9p2_27p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(15z) η(45z)^2 η(135z)` at level 405. -/
abbrev cuspForm_81_eta_3p1_9p2_27p1_old_405_5 : gamma0CuspForms 405 :=
  gamma0Rescale cuspForm_81_eta_3p1_9p2_27p1 5

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_81_eta_3p1_9p2_27p1_old_405_5_eq_eta :
    cuspForm_81_eta_3p1_9p2_27p1_old_405_5 =
      etaQuotientCuspForm 405 sparse![405; 14 => 1, 44 => 2, 134 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_81_eta_3p1_9p2_27p1_old_405_5_first_coeffs :
    first_coeffs 100 cuspForm_81_eta_3p1_9p2_27p1_old_405_5 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
