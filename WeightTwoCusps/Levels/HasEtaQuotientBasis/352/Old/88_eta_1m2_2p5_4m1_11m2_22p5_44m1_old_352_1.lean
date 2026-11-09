module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«88».New.«88_eta_1m2_2p5_4m1_11m2_22p5_44m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 352

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-1) η(11z)^(-2) η(22z)^5 η(44z)^(-1)`; see
[the local level table](../../TABLE.md#level-352).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-1) η(11z)^(-2) η(22z)^5 η(44z)^(-1)` at level 352. -/
abbrev cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1_old_352_1 : gamma0CuspForms 352 :=
  gamma0RescaleToLevel cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1_old_352_1_eq_eta :
    cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1_old_352_1 =
      etaQuotientCuspForm 352 sparse![352; 0 => -2, 1 => 5, 3 => -1, 10 => -2, 21 => 5, 43 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1_old_352_1_first_coeffs :
    first_coeffs 100 cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1_old_352_1 =
    [0, 0, 1, 2, 0, 0, 1, -2, 0, 0, -3, 0, 0, 2, 2, -2, 0, 2, -2, -2,
     0, -6, -1, 2, 0, -4, -4, 2, 0, 4, -3, 2, 0, -2, 6, -2, 0, 0, 8, 2,
     0, 2, 2, 0, 0, 4, -3, 4, 0, 8, 4, -2, 0, -4, -5, 0, 0, -2, 0, -6,
     0, -4, 5, -4, 0, 2, -1, 2, 0, 8, -6, 2, 0, -6, -1, 0, 0, 2, -4, 0,
     0, -4, 0, 4, 0, -6, -10, -4, 0, -8, 6, -4, 0, -8, 0, 6, 0, 4, -3, 0] := by
  eta_coeff

end WeightTwoCusps
