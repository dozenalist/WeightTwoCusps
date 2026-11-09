module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«162».New.«162_eta_1m1_2p2_6m1_9p2_18p2_27m1_81p2_162m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 486

The eta expression is `η(3z)^(-1) η(6z)^2 η(18z)^(-1) η(27z)^2 η(54z)^2 η(81z)^(-1) η(243z)^2 η(486z)^(-1)`; see
[the local level table](../../TABLE.md#level-486).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_162_eta_1m1_2p2_6m1_9p2_18p2_27m1_81p2_162m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-1) η(6z)^2 η(18z)^(-1) η(27z)^2 η(54z)^2 η(81z)^(-1) η(243z)^2 η(486z)^(-1)` at level 486. -/
abbrev cuspForm_162_eta_1m1_2p2_6m1_9p2_18p2_27m1_81p2_162m1_old_486_3 : gamma0CuspForms 486 :=
  gamma0Rescale cuspForm_162_eta_1m1_2p2_6m1_9p2_18p2_27m1_81p2_162m1 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_162_eta_1m1_2p2_6m1_9p2_18p2_27m1_81p2_162m1_old_486_3_eq_eta :
    cuspForm_162_eta_1m1_2p2_6m1_9p2_18p2_27m1_81p2_162m1_old_486_3 =
      etaQuotientCuspForm 486 sparse![486; 2 => -1, 5 => 2, 17 => -1, 26 => 2, 53 => 2, 80 => -1, 242 => 2, 485 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_162_eta_1m1_2p2_6m1_9p2_18p2_27m1_81p2_162m1_old_486_3_first_coeffs :
    first_coeffs 100 cuspForm_162_eta_1m1_2p2_6m1_9p2_18p2_27m1_81p2_162m1_old_486_3 =
    [0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
     0, 2, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 1,
     0, 0, 2, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0,
     -2, 0, 0, 0, 0, 0, -4, 0, 0, -2, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0,
     0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
