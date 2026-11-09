module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«162».New.«162_eta_1m1_2p2_3m1_6p2_9p1_27p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 486

The eta expression is `η(3z)^(-1) η(6z)^2 η(9z)^(-1) η(18z)^2 η(27z) η(81z)`; see
[the local level table](../../TABLE.md#level-486).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_162_eta_1m1_2p2_3m1_6p2_9p1_27p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-1) η(6z)^2 η(9z)^(-1) η(18z)^2 η(27z) η(81z)` at level 486. -/
abbrev cuspForm_162_eta_1m1_2p2_3m1_6p2_9p1_27p1_old_486_3 : gamma0CuspForms 486 :=
  gamma0Rescale cuspForm_162_eta_1m1_2p2_3m1_6p2_9p1_27p1 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_162_eta_1m1_2p2_3m1_6p2_9p1_27p1_old_486_3_eq_eta :
    cuspForm_162_eta_1m1_2p2_3m1_6p2_9p1_27p1_old_486_3 =
      etaQuotientCuspForm 486 sparse![486; 2 => -1, 5 => 2, 8 => -1, 17 => 2, 26 => 1, 80 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_162_eta_1m1_2p2_3m1_6p2_9p1_27p1_old_486_3_first_coeffs :
    first_coeffs 100 cuspForm_162_eta_1m1_2p2_3m1_6p2_9p1_27p1_old_486_3 =
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0,
     0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0,
     0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     -1, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, -2, 0, 0, 0, 0, 0, -1, 0,
     0, 0, 0, 0, 0, 0, 0, -5, 0, 0, -3, 0, 0, 0, 0, 0, -3, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
