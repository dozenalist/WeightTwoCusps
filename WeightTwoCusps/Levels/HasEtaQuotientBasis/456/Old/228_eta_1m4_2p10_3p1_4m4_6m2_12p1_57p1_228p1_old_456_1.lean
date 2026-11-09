module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«228».New.«228_eta_1m4_2p10_3p1_4m4_6m2_12p1_57p1_228p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(6z)^(-2) η(12z) η(57z) η(228z)`; see
[the local level table](../../TABLE.md#level-456).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_228_eta_1m4_2p10_3p1_4m4_6m2_12p1_57p1_228p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(6z)^(-2) η(12z) η(57z) η(228z)` at level 456. -/
abbrev cuspForm_228_eta_1m4_2p10_3p1_4m4_6m2_12p1_57p1_228p1_old_456_1 : gamma0CuspForms 456 :=
  gamma0RescaleToLevel cuspForm_228_eta_1m4_2p10_3p1_4m4_6m2_12p1_57p1_228p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_228_eta_1m4_2p10_3p1_4m4_6m2_12p1_57p1_228p1_old_456_1_eq_eta :
    cuspForm_228_eta_1m4_2p10_3p1_4m4_6m2_12p1_57p1_228p1_old_456_1 =
      etaQuotientCuspForm 456 sparse![456; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 5 => -2, 11 => 1, 56 => 1, 227 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_228_eta_1m4_2p10_3p1_4m4_6m2_12p1_57p1_228p1_old_456_1_first_coeffs :
    first_coeffs 100 cuspForm_228_eta_1m4_2p10_3p1_4m4_6m2_12p1_57p1_228p1_old_456_1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 4, -1, 0, 4, 1, 0,
     0, 2, 4, -4, -2, 0, -4, 1, 0, 4, 0, -8, 0, -1, 0, 0, -2, 0, 0, 0,
     -4, -4, -2, 0, -4, 0, 0, -4, 3, 0, 0, -2, 0, 0, 2, 0, -4, 1, -8, 0,
     0, 0, 4, -2, 0, -4, -2, 4, 4, -3, -4, -4, 1, 0, -4, -1, 0, 4, -1, -4,
     4, 2, 0, 8, 1, 0, -8, 2, 8, -4, 2, 0, 4, 2, 8, 0, -2, 4, 4, 6] := by
  eta_coeff

end WeightTwoCusps
