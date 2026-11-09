module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«162».New.«162_eta_1m1_2p2_3m1_6p2_9p1_27p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 486

The eta expression is `η(z)^(-1) η(2z)^2 η(3z)^(-1) η(6z)^2 η(9z) η(27z)`; see
[the local level table](../../TABLE.md#level-486).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_162_eta_1m1_2p2_3m1_6p2_9p1_27p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(3z)^(-1) η(6z)^2 η(9z) η(27z)` at level 486. -/
abbrev cuspForm_162_eta_1m1_2p2_3m1_6p2_9p1_27p1_old_486_1 : gamma0CuspForms 486 :=
  gamma0RescaleToLevel cuspForm_162_eta_1m1_2p2_3m1_6p2_9p1_27p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_162_eta_1m1_2p2_3m1_6p2_9p1_27p1_old_486_1_eq_eta :
    cuspForm_162_eta_1m1_2p2_3m1_6p2_9p1_27p1_old_486_1 =
      etaQuotientCuspForm 486 sparse![486; 0 => -1, 1 => 2, 2 => -1, 5 => 2, 8 => 1, 26 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_162_eta_1m1_2p2_3m1_6p2_9p1_27p1_old_486_1_first_coeffs :
    first_coeffs 100 cuspForm_162_eta_1m1_2p2_3m1_6p2_9p1_27p1_old_486_1 =
    [0, 0, 1, 1, 0, 2, 1, 0, 2, 0, 0, 1, 1, 0, -1, 0, 0, 0, 0, 0,
     -1, -1, 0, -1, -2, 0, -1, 0, 0, -5, -3, 0, -3, 0, 0, -5, 0, 0, -1, -4,
     0, -1, -1, 0, -5, 0, 0, 4, 1, 0, 1, 0, 0, 3, 0, 0, 1, 2, 0, -4,
     0, 0, 2, 0, 0, -2, 3, 0, 9, 0, 0, 9, 0, 0, -4, 4, 0, 2, 5, 0,
     2, 0, 0, 10, -1, 0, 5, 0, 0, 3, 0, 0, 5, 5, 0, -5, 4, 0, 3, 0] := by
  eta_coeff

end WeightTwoCusps
