module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«110».New.«110_eta_1m1_2p2_5p1_11m1_22p2_55p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 440

The eta expression is `η(2z)^(-1) η(4z)^2 η(10z) η(22z)^(-1) η(44z)^2 η(110z)`; see
[the local level table](../../TABLE.md#level-440).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_110_eta_1m1_2p2_5p1_11m1_22p2_55p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-1) η(4z)^2 η(10z) η(22z)^(-1) η(44z)^2 η(110z)` at level 440. -/
abbrev cuspForm_110_eta_1m1_2p2_5p1_11m1_22p2_55p1_old_440_2 : gamma0CuspForms 440 :=
  gamma0RescaleToLevel cuspForm_110_eta_1m1_2p2_5p1_11m1_22p2_55p1 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_110_eta_1m1_2p2_5p1_11m1_22p2_55p1_old_440_2_eq_eta :
    cuspForm_110_eta_1m1_2p2_5p1_11m1_22p2_55p1_old_440_2 =
      etaQuotientCuspForm 440 sparse![440; 1 => -1, 3 => 2, 9 => 1, 21 => -1, 43 => 2, 109 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_110_eta_1m1_2p2_5p1_11m1_22p2_55p1_old_440_2_first_coeffs :
    first_coeffs 100 cuspForm_110_eta_1m1_2p2_5p1_11m1_22p2_55p1_old_440_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, -1, 0,
     0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 1, 0, -1, 0, 1, 0, 0, 0,
     -2, 0, 0, 0, 0, 0, -1, 0, -2, 0, 1, 0, -2, 0, 0, 0, -1, 0, 0, 0,
     0, 0, -1, 0, 2, 0, 0, 0, 0, 0, -2, 0, 1, 0, 0, 0, 1, 0, 2, 0,
     3, 0, 0, 0, -1, 0, 2, 0, 1, 0, -1, 0, 0, 0, 0, 0, -3, 0, 2, 0] := by
  eta_coeff

end WeightTwoCusps
