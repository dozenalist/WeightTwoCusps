module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«114».New.«114_eta_1m2_2p3_3p3_6m2_38p1_57p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^3 η(6z)^(-2) η(38z) η(57z)`; see
[the local level table](../../TABLE.md#level-456).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_114_eta_1m2_2p3_3p3_6m2_38p1_57p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^3 η(6z)^(-2) η(38z) η(57z)` at level 456. -/
abbrev cuspForm_114_eta_1m2_2p3_3p3_6m2_38p1_57p1_old_456_1 : gamma0CuspForms 456 :=
  gamma0RescaleToLevel cuspForm_114_eta_1m2_2p3_3p3_6m2_38p1_57p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_114_eta_1m2_2p3_3p3_6m2_38p1_57p1_old_456_1_eq_eta :
    cuspForm_114_eta_1m2_2p3_3p3_6m2_38p1_57p1_old_456_1 =
      etaQuotientCuspForm 456 sparse![456; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 37 => 1, 56 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_114_eta_1m2_2p3_3p3_6m2_38p1_57p1_old_456_1_first_coeffs :
    first_coeffs 100 cuspForm_114_eta_1m2_2p3_3p3_6m2_38p1_57p1_old_456_1 =
    [0, 0, 0, 0, 1, 2, 2, 1, -1, 0, 0, 1, 1, -3, -2, -3, 1, 1, -2, 1,
     -3, -1, -1, -1, 0, -3, 1, 0, -2, 1, 1, 2, -1, 0, 0, -3, 1, 0, 0, -1,
     3, 3, 0, -3, 0, 2, 0, 2, -3, -1, -1, 4, 4, 2, 0, 3, 3, -1, 4, 0,
     1, 1, 1, 1, -3, 1, 4, -1, -2, -3, 1, 1, 3, 1, -1, 5, -1, 3, -3, -1,
     1, 0, 0, -8, 2, -3, 1, -4, -2, 3, -6, 6, -1, -5, 0, -1, 4, -1, -2, 1] := by
  eta_coeff

end WeightTwoCusps
