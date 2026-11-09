module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«80».New.«80_eta_1m2_2p5_4m1_5m2_10p5_20m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 160

The eta expression is `η(2z)^(-2) η(4z)^5 η(8z)^(-1) η(10z)^(-2) η(20z)^5 η(40z)^(-1)`; see
[the local level table](../../TABLE.md#level-160).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_80_eta_1m2_2p5_4m1_5m2_10p5_20m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-2) η(4z)^5 η(8z)^(-1) η(10z)^(-2) η(20z)^5 η(40z)^(-1)` at level 160. -/
abbrev cuspForm_80_eta_1m2_2p5_4m1_5m2_10p5_20m1_old_160_2 : gamma0CuspForms 160 :=
  gamma0Rescale cuspForm_80_eta_1m2_2p5_4m1_5m2_10p5_20m1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_80_eta_1m2_2p5_4m1_5m2_10p5_20m1_old_160_2_eq_eta :
    cuspForm_80_eta_1m2_2p5_4m1_5m2_10p5_20m1_old_160_2 =
      etaQuotientCuspForm 160 sparse![160; 1 => -2, 3 => 5, 7 => -1, 9 => -2, 19 => 5, 39 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_80_eta_1m2_2p5_4m1_5m2_10p5_20m1_old_160_2_first_coeffs :
    first_coeffs 100 cuspForm_80_eta_1m2_2p5_4m1_5m2_10p5_20m1_old_160_2 =
    [0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, -3, 0,
     2, 0, -4, 0, 0, 0, -2, 0, -8, 0, 0, 0, 0, 0, 2, 0, -6, 0, -4, 0,
     0, 0, 0, 0, 8, 0, -4, 0, 0, 0, 1, 0, -4, 0, 0, 0, 0, 0, -2, 0,
     0, 0, 8, 0, 0, 0, 0, 0, 4, 0, 4, 0, 0, 0, 6, 0, 8, 0, 0, 0,
     0, 0, -6, 0, 0, 0, 8, 0, 0, 0, -3, 0, 8, 0, -4, 0, 0, 0, 9, 0] := by
  eta_coeff

end WeightTwoCusps
