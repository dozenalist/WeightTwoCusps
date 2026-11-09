module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«228».New.«228_eta_1m2_2p5_4m2_6p1_19p1_38m1_57m1_76p1_114p3_228m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(6z) η(19z) η(38z)^(-1) η(57z)^(-1) η(76z) η(114z)^3 η(228z)^(-1)`; see
[the local level table](../../TABLE.md#level-456).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_228_eta_1m2_2p5_4m2_6p1_19p1_38m1_57m1_76p1_114p3_228m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(6z) η(19z) η(38z)^(-1) η(57z)^(-1) η(76z) η(114z)^3 η(228z)^(-1)` at level 456. -/
abbrev cuspForm_228_eta_1m2_2p5_4m2_6p1_19p1_38m1_57m1_76p1_114p3_228m1_old_456_1 : gamma0CuspForms 456 :=
  gamma0RescaleToLevel cuspForm_228_eta_1m2_2p5_4m2_6p1_19p1_38m1_57m1_76p1_114p3_228m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_228_eta_1m2_2p5_4m2_6p1_19p1_38m1_57m1_76p1_114p3_228m1_old_456_1_eq_eta :
    cuspForm_228_eta_1m2_2p5_4m2_6p1_19p1_38m1_57m1_76p1_114p3_228m1_old_456_1 =
      etaQuotientCuspForm 456 sparse![456; 0 => -2, 1 => 5, 3 => -2, 5 => 1, 18 => 1, 37 => -1, 56 => -1, 75 => 1, 113 => 3, 227 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_228_eta_1m2_2p5_4m2_6p1_19p1_38m1_57m1_76p1_114p3_228m1_old_456_1_first_coeffs :
    first_coeffs 100 cuspForm_228_eta_1m2_2p5_4m2_6p1_19p1_38m1_57m1_76p1_114p3_228m1_old_456_1 =
    [0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, -1, -2, 0, 2, -2, 0, -1, -2, 0,
     -2, 0, 0, 0, -1, -2, -2, -2, -2, 0, 3, 2, 0, -4, 2, 1, 1, 2, 0, 4,
     0, 2, -2, 0, 2, 2, 2, -1, 2, -2, 0, 4, 2, -2, 1, 0, 2, 0, -2, 0,
     -2, 2, 0, 0, 0, 0, -1, -2, 0, 2, -4, 2, 4, -2, 0, -4, 0, -1, -2, 0,
     0, -5, -4, 2, 2, 0, 0, 1, 0, 0, -4, 0, -2, -1, 4, -1, 3, 2, -2, 0] := by
  eta_coeff

end WeightTwoCusps
