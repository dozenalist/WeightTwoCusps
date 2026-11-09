module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«42».New.«42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 462

The eta expression is `η(z)^(-1) η(2z) η(3z)^4 η(6z)^(-2) η(7z) η(14z)^(-1) η(21z)^(-2) η(42z)^4`; see
[the local level table](../../TABLE.md#level-462).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z)^4 η(6z)^(-2) η(7z) η(14z)^(-1) η(21z)^(-2) η(42z)^4` at level 462. -/
abbrev cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_462_1 : gamma0CuspForms 462 :=
  gamma0RescaleToLevel cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_462_1_eq_eta :
    cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_462_1 =
      etaQuotientCuspForm 462 sparse![462; 0 => -1, 1 => 1, 2 => 4, 5 => -2, 6 => 1, 13 => -1, 20 => -2, 41 => 4] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_462_1_first_coeffs :
    first_coeffs 100 cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_462_1 =
    [0, 0, 0, 0, 0, 1, 1, 1, -2, -2, -1, 0, 0, -3, -1, 0, 2, 4, 2, 1,
     1, 0, 4, -2, -1, -2, -1, 3, 1, -2, -2, -2, 0, -2, -8, -1, -2, 2, 3, 2,
     3, 4, -1, 6, 0, 1, -2, -6, 2, 0, 2, 2, -3, 0, -2, 0, 1, -2, 2, -7,
     0, 3, 2, -1, -4, 2, 2, -4, 4, 2, 1, -2, 0, 0, 6, 0, 1, 0, 0, 8,
     -3, -2, 0, 1, 0, -2, -6, 0, -4, 2, -1, -1, -2, 0, 6, 0, 1, -6, 0, 0] := by
  eta_coeff

end WeightTwoCusps
