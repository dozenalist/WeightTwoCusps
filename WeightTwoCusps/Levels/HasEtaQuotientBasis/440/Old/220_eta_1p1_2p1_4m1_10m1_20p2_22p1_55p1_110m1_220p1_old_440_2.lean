module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«220».New.«220_eta_1p1_2p1_4m1_10m1_20p2_22p1_55p1_110m1_220p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 440

The eta expression is `η(2z) η(4z) η(8z)^(-1) η(20z)^(-1) η(40z)^2 η(44z) η(110z) η(220z)^(-1) η(440z)`; see
[the local level table](../../TABLE.md#level-440).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_220_eta_1p1_2p1_4m1_10m1_20p2_22p1_55p1_110m1_220p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(4z) η(8z)^(-1) η(20z)^(-1) η(40z)^2 η(44z) η(110z) η(220z)^(-1) η(440z)` at level 440. -/
abbrev cuspForm_220_eta_1p1_2p1_4m1_10m1_20p2_22p1_55p1_110m1_220p1_old_440_2 : gamma0CuspForms 440 :=
  gamma0Rescale cuspForm_220_eta_1p1_2p1_4m1_10m1_20p2_22p1_55p1_110m1_220p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_220_eta_1p1_2p1_4m1_10m1_20p2_22p1_55p1_110m1_220p1_old_440_2_eq_eta :
    cuspForm_220_eta_1p1_2p1_4m1_10m1_20p2_22p1_55p1_110m1_220p1_old_440_2 =
      etaQuotientCuspForm 440 sparse![440; 1 => 1, 3 => 1, 7 => -1, 19 => -1, 39 => 2, 43 => 1, 109 => 1, 219 => -1, 439 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_220_eta_1p1_2p1_4m1_10m1_20p2_22p1_55p1_110m1_220p1_old_440_2_first_coeffs :
    first_coeffs 100 cuspForm_220_eta_1p1_2p1_4m1_10m1_20p2_22p1_55p1_110m1_220p1_old_440_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
     -1, 0, -2, 0, 1, 0, 1, 0, 1, 0, -1, 0, 1, 0, 2, 0, -2, 0, -1, 0,
     -1, 0, -1, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, -1, 0, 0, 0, 1, 0,
     0, 0, -2, 0, 1, 0, 4, 0, -3, 0, -2, 0, 0, 0, 0, 0, 0, 0, -2, 0,
     3, 0, 2, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, -3, 0, 0, 0, 1, 0] := by
  eta_coeff

end WeightTwoCusps
