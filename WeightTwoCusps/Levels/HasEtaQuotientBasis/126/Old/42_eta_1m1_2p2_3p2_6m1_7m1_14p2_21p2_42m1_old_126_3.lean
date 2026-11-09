module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«42».New.«42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 126

The eta expression is `η(3z)^(-1) η(6z)^2 η(9z)^2 η(18z)^(-1) η(21z)^(-1) η(42z)^2 η(63z)^2 η(126z)^(-1)`; see
[the local level table](../../TABLE.md#level-126).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-1) η(6z)^2 η(9z)^2 η(18z)^(-1) η(21z)^(-1) η(42z)^2 η(63z)^2 η(126z)^(-1)` at level 126. -/
abbrev cuspForm_42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1_old_126_3 : gamma0CuspForms 126 :=
  gamma0Rescale cuspForm_42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1_old_126_3_eq_eta :
    cuspForm_42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1_old_126_3 =
      etaQuotientCuspForm 126 sparse![126; 2 => -1, 5 => 2, 8 => 2, 17 => -1, 20 => -1, 41 => 2, 62 => 2, 125 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1_old_126_3_first_coeffs :
    first_coeffs 100 cuspForm_42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1_old_126_3 =
    [0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, -2, 0, 0, 0, 0,
     0, -1, 0, 0, 1, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0, 0, -2, 0, 0, 2,
     0, 0, -1, 0, 0, 0, 0, 0, 3, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0,
     2, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, -1, 0, 0, 2, 0,
     0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 4] := by
  eta_coeff

end WeightTwoCusps
