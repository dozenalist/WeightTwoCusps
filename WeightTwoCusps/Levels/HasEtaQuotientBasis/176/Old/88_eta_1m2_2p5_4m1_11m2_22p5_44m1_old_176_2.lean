module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«88».New.«88_eta_1m2_2p5_4m1_11m2_22p5_44m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 176

The eta expression is `η(2z)^(-2) η(4z)^5 η(8z)^(-1) η(22z)^(-2) η(44z)^5 η(88z)^(-1)`; see
[the local level table](../../TABLE.md#level-176).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-2) η(4z)^5 η(8z)^(-1) η(22z)^(-2) η(44z)^5 η(88z)^(-1)` at level 176. -/
abbrev cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1_old_176_2 : gamma0CuspForms 176 :=
  gamma0Rescale cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1_old_176_2_eq_eta :
    cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1_old_176_2 =
      etaQuotientCuspForm 176 sparse![176; 1 => -2, 3 => 5, 7 => -1, 21 => -2, 43 => 5, 87 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1_old_176_2_first_coeffs :
    first_coeffs 100 cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1_old_176_2 =
    [0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 1, 0, -2, 0, 0, 0, 0, 0,
     -3, 0, 0, 0, 0, 0, 2, 0, 2, 0, -2, 0, 0, 0, 2, 0, -2, 0, -2, 0,
     0, 0, -6, 0, -1, 0, 2, 0, 0, 0, -4, 0, -4, 0, 2, 0, 0, 0, 4, 0,
     -3, 0, 2, 0, 0, 0, -2, 0, 6, 0, -2, 0, 0, 0, 0, 0, 8, 0, 2, 0,
     0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 4, 0, -3, 0, 4, 0, 0, 0, 8, 0] := by
  eta_coeff

end WeightTwoCusps
