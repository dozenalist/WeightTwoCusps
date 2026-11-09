module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«64».New.«64_eta_1m2_2p5_4m2_8p3»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 320

The eta expression is `η(5z)^(-2) η(10z)^5 η(20z)^(-2) η(40z)^3`; see
[the local level table](../../TABLE.md#level-320).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(5z)` of `cuspForm_64_eta_1m2_2p5_4m2_8p3`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(5z)^(-2) η(10z)^5 η(20z)^(-2) η(40z)^3` at level 320. -/
abbrev cuspForm_64_eta_1m2_2p5_4m2_8p3_old_320_5 : gamma0CuspForms 320 :=
  gamma0Rescale cuspForm_64_eta_1m2_2p5_4m2_8p3 5

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_64_eta_1m2_2p5_4m2_8p3_old_320_5_eq_eta :
    cuspForm_64_eta_1m2_2p5_4m2_8p3_old_320_5 =
      etaQuotientCuspForm 320 sparse![320; 4 => -2, 9 => 5, 19 => -2, 39 => 3] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_64_eta_1m2_2p5_4m2_8p3_old_320_5_first_coeffs :
    first_coeffs 100 cuspForm_64_eta_1m2_2p5_4m2_8p3_old_320_5 =
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, -3, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 2, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
