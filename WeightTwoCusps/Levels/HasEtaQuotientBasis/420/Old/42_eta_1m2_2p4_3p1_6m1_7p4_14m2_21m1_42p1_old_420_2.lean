module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«42».New.«42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(2z)^(-2) η(4z)^4 η(6z) η(12z)^(-1) η(14z)^4 η(28z)^(-2) η(42z)^(-1) η(84z)`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-2) η(4z)^4 η(6z) η(12z)^(-1) η(14z)^4 η(28z)^(-2) η(42z)^(-1) η(84z)` at level 420. -/
abbrev cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_420_2 : gamma0CuspForms 420 :=
  gamma0RescaleToLevel cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_420_2_eq_eta :
    cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_420_2 =
      etaQuotientCuspForm 420 sparse![420; 1 => -2, 3 => 4, 5 => 1, 11 => -1, 13 => 4, 27 => -2, 41 => -1, 83 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_420_2_first_coeffs :
    first_coeffs 100 cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_420_2 =
    [0, 0, 1, 0, 2, 0, 1, 0, 1, 0, 0, 0, -1, 0, 1, 0, -4, 0, -8, 0,
     -6, 0, -6, 0, 1, 0, 2, 0, -4, 0, 3, 0, 7, 0, 12, 0, 11, 0, -4, 0,
     0, 0, 4, 0, 6, 0, 6, 0, -7, 0, -5, 0, 4, 0, 7, 0, 1, 0, -6, 0,
     -3, 0, -4, 0, 2, 0, 0, 0, -18, 0, 0, 0, -8, 0, -10, 0, 4, 0, -13, 0,
     6, 0, 0, 0, -4, 0, 8, 0, -6, 0, 0, 0, 6, 0, -12, 0, 7, 0, 1, 0] := by
  eta_coeff

end WeightTwoCusps
