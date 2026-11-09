module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«176».New.«176_eta_1m2_2p6_4m2_22p1_44m2_88p5_176m2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 352

The eta expression is `η(2z)^(-2) η(4z)^6 η(8z)^(-2) η(44z) η(88z)^(-2) η(176z)^5 η(352z)^(-2)`; see
[the local level table](../../TABLE.md#level-352).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_176_eta_1m2_2p6_4m2_22p1_44m2_88p5_176m2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-2) η(4z)^6 η(8z)^(-2) η(44z) η(88z)^(-2) η(176z)^5 η(352z)^(-2)` at level 352. -/
abbrev cuspForm_176_eta_1m2_2p6_4m2_22p1_44m2_88p5_176m2_old_352_2 : gamma0CuspForms 352 :=
  gamma0Rescale cuspForm_176_eta_1m2_2p6_4m2_22p1_44m2_88p5_176m2 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_176_eta_1m2_2p6_4m2_22p1_44m2_88p5_176m2_old_352_2_eq_eta :
    cuspForm_176_eta_1m2_2p6_4m2_22p1_44m2_88p5_176m2_old_352_2 =
      etaQuotientCuspForm 352 sparse![352; 1 => -2, 3 => 6, 7 => -2, 43 => 1, 87 => -2, 175 => 5, 351 => -2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_176_eta_1m2_2p6_4m2_22p1_44m2_88p5_176m2_old_352_2_first_coeffs :
    first_coeffs 100 cuspForm_176_eta_1m2_2p6_4m2_22p1_44m2_88p5_176m2_old_352_2 =
    [0, 0, 1, 0, 2, 0, -1, 0, -2, 0, 1, 0, -2, 0, -2, 0, 0, 0, -2, 0,
     2, 0, 1, 0, 0, 0, 0, 0, -2, 0, 3, 0, 2, 0, 2, 0, 0, 0, 0, 0,
     2, 0, -2, 0, 0, 0, -1, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0,
     -2, 0, 3, 0, -4, 0, -1, 0, -2, 0, -2, 0, 4, 0, -1, 0, -2, 0, -4, 0,
     0, 0, -4, 0, -2, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 0, -2, 0, 1, 0] := by
  eta_coeff

end WeightTwoCusps
