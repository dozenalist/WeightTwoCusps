module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«110».New.«110_eta_1m1_2p2_10p1_11p1_55p2_110m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 440

The eta expression is `η(4z)^(-1) η(8z)^2 η(40z) η(44z) η(220z)^2 η(440z)^(-1)`; see
[the local level table](../../TABLE.md#level-440).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_110_eta_1m1_2p2_10p1_11p1_55p2_110m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^(-1) η(8z)^2 η(40z) η(44z) η(220z)^2 η(440z)^(-1)` at level 440. -/
abbrev cuspForm_110_eta_1m1_2p2_10p1_11p1_55p2_110m1_old_440_4 : gamma0CuspForms 440 :=
  gamma0Rescale cuspForm_110_eta_1m1_2p2_10p1_11p1_55p2_110m1 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_110_eta_1m1_2p2_10p1_11p1_55p2_110m1_old_440_4_eq_eta :
    cuspForm_110_eta_1m1_2p2_10p1_11p1_55p2_110m1_old_440_4 =
      etaQuotientCuspForm 440 sparse![440; 3 => -1, 7 => 2, 39 => 1, 43 => 1, 219 => 2, 439 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_110_eta_1m1_2p2_10p1_11p1_55p2_110m1_old_440_4_first_coeffs :
    first_coeffs 100 cuspForm_110_eta_1m1_2p2_10p1_11p1_55p2_110m1_old_440_4 =
    [0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0,
     -1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
