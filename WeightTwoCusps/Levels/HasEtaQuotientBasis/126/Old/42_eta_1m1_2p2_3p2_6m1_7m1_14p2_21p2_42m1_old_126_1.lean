module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«42».New.«42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 126

The eta expression is `η(z)^(-1) η(2z)^2 η(3z)^2 η(6z)^(-1) η(7z)^(-1) η(14z)^2 η(21z)^2 η(42z)^(-1)`; see
[the local level table](../../TABLE.md#level-126).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(3z)^2 η(6z)^(-1) η(7z)^(-1) η(14z)^2 η(21z)^2 η(42z)^(-1)` at level 126. -/
abbrev cuspForm_42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1_old_126_1 : gamma0CuspForms 126 :=
  gamma0RescaleToLevel cuspForm_42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1_old_126_1_eq_eta :
    cuspForm_42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1_old_126_1 =
      etaQuotientCuspForm 126 sparse![126; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 6 => -1, 13 => 2, 20 => 2, 41 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1_old_126_1_first_coeffs :
    first_coeffs 100 cuspForm_42_eta_1m1_2p2_3p2_6m1_7m1_14p2_21p2_42m1_old_126_1 =
    [0, 1, 1, 0, -1, -2, 0, -1, 1, 1, -2, 0, -2, 2, -1, 0, 3, -2, 1, 0,
     2, 0, 0, 4, 0, -1, 2, 0, 1, -2, 0, 0, -3, 4, -2, 2, -1, -2, 0, -4,
     -2, -2, 0, -4, -8, -2, 4, 0, 2, 1, -1, -4, 6, 6, 0, 0, -1, 4, -2, 8,
     4, 2, 0, -1, -1, -4, 4, 4, 10, -4, 2, 4, 1, 2, -2, 0, -8, 0, -4, -8,
     -6, 1, -2, -8, 2, 4, -4, 0, 0, -10, -2, -2, 4, 0, 0, 0, -4, 2, 1, 0] := by
  eta_coeff

end WeightTwoCusps
