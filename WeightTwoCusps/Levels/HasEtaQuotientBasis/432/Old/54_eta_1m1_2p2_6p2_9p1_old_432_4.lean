module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«54».New.«54_eta_1m1_2p2_6p2_9p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 432

The eta expression is `η(4z)^(-1) η(8z)^2 η(24z)^2 η(36z)`; see
[the local level table](../../TABLE.md#level-432).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_54_eta_1m1_2p2_6p2_9p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^(-1) η(8z)^2 η(24z)^2 η(36z)` at level 432. -/
abbrev cuspForm_54_eta_1m1_2p2_6p2_9p1_old_432_4 : gamma0CuspForms 432 :=
  gamma0RescaleToLevel cuspForm_54_eta_1m1_2p2_6p2_9p1 4 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_54_eta_1m1_2p2_6p2_9p1_old_432_4_eq_eta :
    cuspForm_54_eta_1m1_2p2_6p2_9p1_old_432_4 =
      etaQuotientCuspForm 432 sparse![432; 3 => -1, 7 => 2, 23 => 2, 35 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_54_eta_1m1_2p2_6p2_9p1_old_432_4_first_coeffs :
    first_coeffs 100 cuspForm_54_eta_1m1_2p2_6p2_9p1_old_432_4 =
    [0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0,
     -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, -1, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
