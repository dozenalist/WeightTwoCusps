module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«88».New.«88_eta_1m2_2p5_4m1_11m2_22p5_44m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 440

The eta expression is `η(5z)^(-2) η(10z)^5 η(20z)^(-1) η(55z)^(-2) η(110z)^5 η(220z)^(-1)`; see
[the local level table](../../TABLE.md#level-440).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(5z)` of `cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(5z)^(-2) η(10z)^5 η(20z)^(-1) η(55z)^(-2) η(110z)^5 η(220z)^(-1)` at level 440. -/
abbrev cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1_old_440_5 : gamma0CuspForms 440 :=
  gamma0Rescale cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1 5

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1_old_440_5_eq_eta :
    cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1_old_440_5 =
      etaQuotientCuspForm 440 sparse![440; 4 => -2, 9 => 5, 19 => -1, 54 => -2, 109 => 5, 219 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1_old_440_5_first_coeffs :
    first_coeffs 100 cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1_old_440_5 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -2, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, -2, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 2, 0, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
