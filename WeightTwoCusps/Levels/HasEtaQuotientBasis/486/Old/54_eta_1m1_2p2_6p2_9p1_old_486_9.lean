module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«54».New.«54_eta_1m1_2p2_6p2_9p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 486

The eta expression is `η(9z)^(-1) η(18z)^2 η(54z)^2 η(81z)`; see
[the local level table](../../TABLE.md#level-486).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(9z)` of `cuspForm_54_eta_1m1_2p2_6p2_9p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(9z)^(-1) η(18z)^2 η(54z)^2 η(81z)` at level 486. -/
abbrev cuspForm_54_eta_1m1_2p2_6p2_9p1_old_486_9 : gamma0CuspForms 486 :=
  gamma0Rescale cuspForm_54_eta_1m1_2p2_6p2_9p1 9

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_54_eta_1m1_2p2_6p2_9p1_old_486_9_eq_eta :
    cuspForm_54_eta_1m1_2p2_6p2_9p1_old_486_9 =
      etaQuotientCuspForm 486 sparse![486; 8 => -1, 17 => 2, 53 => 2, 80 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_54_eta_1m1_2p2_6p2_9p1_old_486_9_first_coeffs :
    first_coeffs 100 cuspForm_54_eta_1m1_2p2_6p2_9p1_old_486_9 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
