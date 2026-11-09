module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«88».New.«88_eta_1m2_2p5_4m1_11m2_22p5_44m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 352

The eta expression is `η(4z)^(-2) η(8z)^5 η(16z)^(-1) η(44z)^(-2) η(88z)^5 η(176z)^(-1)`; see
[the local level table](../../TABLE.md#level-352).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^(-2) η(8z)^5 η(16z)^(-1) η(44z)^(-2) η(88z)^5 η(176z)^(-1)` at level 352. -/
abbrev cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1_old_352_4 : gamma0CuspForms 352 :=
  gamma0Rescale cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1_old_352_4_eq_eta :
    cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1_old_352_4 =
      etaQuotientCuspForm 352 sparse![352; 3 => -2, 7 => 5, 15 => -1, 43 => -2, 87 => 5, 175 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1_old_352_4_first_coeffs :
    first_coeffs 100 cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1_old_352_4 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0,
     -2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, -2, 0, 0, 0, -2, 0, 0, 0,
     0, 0, 0, 0, -6, 0, 0, 0, -1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
