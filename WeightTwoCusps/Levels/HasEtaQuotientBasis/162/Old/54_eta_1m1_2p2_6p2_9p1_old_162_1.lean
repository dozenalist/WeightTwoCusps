module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«54».New.«54_eta_1m1_2p2_6p2_9p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 162

The eta expression is `η(z)^(-1) η(2z)^2 η(6z)^2 η(9z)`; see
[the local level table](../../TABLE.md#level-162).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_54_eta_1m1_2p2_6p2_9p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(6z)^2 η(9z)` at level 162. -/
abbrev cuspForm_54_eta_1m1_2p2_6p2_9p1_old_162_1 : gamma0CuspForms 162 :=
  gamma0RescaleToLevel cuspForm_54_eta_1m1_2p2_6p2_9p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_54_eta_1m1_2p2_6p2_9p1_old_162_1_eq_eta :
    cuspForm_54_eta_1m1_2p2_6p2_9p1_old_162_1 =
      etaQuotientCuspForm 162 sparse![162; 0 => -1, 1 => 2, 5 => 2, 8 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_54_eta_1m1_2p2_6p2_9p1_old_162_1_first_coeffs :
    first_coeffs 100 cuspForm_54_eta_1m1_2p2_6p2_9p1_old_162_1 =
    [0, 1, 1, 0, 1, 0, 0, -1, -2, 0, -3, 0, 0, -4, -1, 0, 1, 0, 0, 2,
     0, 0, 3, 0, 0, 4, 5, 0, -1, 0, 0, 5, 4, 0, 0, 0, 0, 2, -7, 0,
     -3, 0, 0, -10, 0, 0, 6, 0, 0, -6, -5, 0, -4, 0, 0, -9, 2, 0, -6, 0,
     0, 8, -4, 0, 1, 0, 0, 14, 0, 0, 3, 0, 0, -7, 11, 0, 2, 0, 0, 8,
     0, 0, 6, 0, 0, 0, 8, 0, 3, 0, 0, 4, 0, 0, -6, 0, 0, -1, -6, 0] := by
  eta_coeff

end WeightTwoCusps
