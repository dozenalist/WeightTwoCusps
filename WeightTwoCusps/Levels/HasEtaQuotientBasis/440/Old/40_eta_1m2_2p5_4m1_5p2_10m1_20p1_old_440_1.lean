module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«40».New.«40_eta_1m2_2p5_4m1_5p2_10m1_20p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 440

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-1) η(5z)^2 η(10z)^(-1) η(20z)`; see
[the local level table](../../TABLE.md#level-440).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-1) η(5z)^2 η(10z)^(-1) η(20z)` at level 440. -/
abbrev cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_440_1 : gamma0CuspForms 440 :=
  gamma0RescaleToLevel cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_440_1_eq_eta :
    cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_440_1 =
      etaQuotientCuspForm 440 sparse![440; 0 => -2, 1 => 5, 3 => -1, 4 => 2, 9 => -1, 19 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_440_1_first_coeffs :
    first_coeffs 100 cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_440_1 =
    [0, 1, 2, 0, 0, 1, -4, -4, 0, -3, -2, 4, 0, -2, 4, 0, 0, 2, 2, 4,
     0, 0, 0, 4, 0, 1, 4, 0, 0, -2, 4, -8, 0, 0, -12, -4, 0, 6, -8, 0,
     0, -6, -8, -8, 0, -3, 12, 4, 0, 9, 2, 0, 0, 6, 8, 4, 0, 0, 12, -4,
     0, -2, -8, 12, 0, -2, 0, 8, 0, 0, -4, 0, 0, -6, 4, 0, 0, -16, -8, 0,
     0, 9, 12, -16, 0, 2, -20, 0, 0, -6, -2, 8, 0, 0, -12, 4, 0, -14, -6, -12] := by
  eta_coeff

end WeightTwoCusps
