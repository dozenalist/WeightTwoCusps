module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«234».New.«234_eta_1m2_2p3_3p3_6m2_13p1_26m1_39m2_78p3_117p2_234m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^3 η(6z)^(-2) η(13z) η(26z)^(-1) η(39z)^(-2) η(78z)^3 η(117z)^2 η(234z)^(-1)`; see
[the local level table](../../TABLE.md#level-468).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_234_eta_1m2_2p3_3p3_6m2_13p1_26m1_39m2_78p3_117p2_234m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^3 η(6z)^(-2) η(13z) η(26z)^(-1) η(39z)^(-2) η(78z)^3 η(117z)^2 η(234z)^(-1)` at level 468. -/
abbrev cuspForm_234_eta_1m2_2p3_3p3_6m2_13p1_26m1_39m2_78p3_117p2_234m1_old_468_1 : gamma0CuspForms 468 :=
  gamma0RescaleToLevel cuspForm_234_eta_1m2_2p3_3p3_6m2_13p1_26m1_39m2_78p3_117p2_234m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_234_eta_1m2_2p3_3p3_6m2_13p1_26m1_39m2_78p3_117p2_234m1_old_468_1_eq_eta :
    cuspForm_234_eta_1m2_2p3_3p3_6m2_13p1_26m1_39m2_78p3_117p2_234m1_old_468_1 =
      etaQuotientCuspForm 468 sparse![468; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 12 => 1, 25 => -1, 38 => -2, 77 => 3, 116 => 2, 233 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_234_eta_1m2_2p3_3p3_6m2_13p1_26m1_39m2_78p3_117p2_234m1_old_468_1_first_coeffs :
    first_coeffs 100 cuspForm_234_eta_1m2_2p3_3p3_6m2_13p1_26m1_39m2_78p3_117p2_234m1_old_468_1 =
    [0, 0, 0, 0, 0, 0, 1, 2, 2, 1, -1, 0, 0, 1, 1, -3, -2, -3, 1, 0,
     -4, -1, -4, 0, -1, -1, -1, -4, 4, 2, 1, 0, 0, 4, -2, 3, 1, -2, 2, 0,
     3, -2, 3, 5, 0, -1, 2, 6, 0, 1, 0, -1, 1, 2, 0, -6, -5, 4, 2, -6,
     -3, -4, -2, 3, 2, -1, -6, 2, 5, 0, -4, -2, -1, -6, 3, 1, -2, 2, -1, 2,
     0, 4, 10, 0, -1, 4, 6, 0, 2, -2, -2, 1, 0, 2, -9, -4, 1, 0, -4, -2] := by
  eta_coeff

end WeightTwoCusps
