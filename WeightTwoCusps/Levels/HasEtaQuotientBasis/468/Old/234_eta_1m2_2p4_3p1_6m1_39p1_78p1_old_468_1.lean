module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«234».New.«234_eta_1m2_2p4_3p1_6m1_39p1_78p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-2) η(2z)^4 η(3z) η(6z)^(-1) η(39z) η(78z)`; see
[the local level table](../../TABLE.md#level-468).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_234_eta_1m2_2p4_3p1_6m1_39p1_78p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z) η(6z)^(-1) η(39z) η(78z)` at level 468. -/
abbrev cuspForm_234_eta_1m2_2p4_3p1_6m1_39p1_78p1_old_468_1 : gamma0CuspForms 468 :=
  gamma0RescaleToLevel cuspForm_234_eta_1m2_2p4_3p1_6m1_39p1_78p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_234_eta_1m2_2p4_3p1_6m1_39p1_78p1_old_468_1_eq_eta :
    cuspForm_234_eta_1m2_2p4_3p1_6m1_39p1_78p1_old_468_1 =
      etaQuotientCuspForm 468 sparse![468; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 38 => 1, 77 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_234_eta_1m2_2p4_3p1_6m1_39p1_78p1_old_468_1_first_coeffs :
    first_coeffs 100 cuspForm_234_eta_1m2_2p4_3p1_6m1_39p1_78p1_old_468_1 =
    [0, 0, 0, 0, 0, 1, 2, 1, 1, 0, -1, 1, 0, 0, -2, -2, 1, -2, 0, -1,
     -1, 0, -1, 0, -4, 0, 1, 0, 0, -2, 0, 0, 0, 2, 1, -2, 0, -1, 0, 0,
     1, 3, 0, 0, 1, -2, -1, 1, 0, 0, -2, 4, 0, 2, 2, 0, 4, 0, 2, -1,
     2, 2, 2, 4, 0, -1, 0, 0, 2, 0, -1, 1, -2, -1, 2, 0, 0, 2, 0, -2,
     -5, 0, 1, -3, -4, -1, -4, -4, 3, -3, -4, 0, 0, 4, -3, 2, 2, 1, 4, -2] := by
  eta_coeff

end WeightTwoCusps
