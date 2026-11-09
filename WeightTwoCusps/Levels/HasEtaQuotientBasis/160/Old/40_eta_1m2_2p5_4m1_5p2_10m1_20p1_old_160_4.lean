module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«40».New.«40_eta_1m2_2p5_4m1_5p2_10m1_20p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 160

The eta expression is `η(4z)^(-2) η(8z)^5 η(16z)^(-1) η(20z)^2 η(40z)^(-1) η(80z)`; see
[the local level table](../../TABLE.md#level-160).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^(-2) η(8z)^5 η(16z)^(-1) η(20z)^2 η(40z)^(-1) η(80z)` at level 160. -/
abbrev cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_160_4 : gamma0CuspForms 160 :=
  gamma0Rescale cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_160_4_eq_eta :
    cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_160_4 =
      etaQuotientCuspForm 160 sparse![160; 3 => -2, 7 => 5, 15 => -1, 19 => 2, 39 => -1, 79 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_160_4_first_coeffs :
    first_coeffs 100 cuspForm_40_eta_1m2_2p5_4m1_5p2_10m1_20p1_old_160_4 =
    [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, -4, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0,
     -2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 4, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
