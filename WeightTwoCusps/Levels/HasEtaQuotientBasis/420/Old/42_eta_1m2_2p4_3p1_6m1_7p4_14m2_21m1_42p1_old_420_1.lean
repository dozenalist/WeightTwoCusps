module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«42».New.«42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(z)^(-2) η(2z)^4 η(3z) η(6z)^(-1) η(7z)^4 η(14z)^(-2) η(21z)^(-1) η(42z)`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z) η(6z)^(-1) η(7z)^4 η(14z)^(-2) η(21z)^(-1) η(42z)` at level 420. -/
abbrev cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_420_1 : gamma0CuspForms 420 :=
  gamma0RescaleToLevel cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_420_1_eq_eta :
    cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_420_1 =
      etaQuotientCuspForm 420 sparse![420; 0 => -2, 1 => 4, 2 => 1, 5 => -1, 6 => 4, 13 => -2, 20 => -1, 41 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_420_1_first_coeffs :
    first_coeffs 100 cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_420_1 =
    [0, 1, 2, 1, 1, 0, -1, 1, -4, -8, -6, -6, 1, 2, -4, 3, 7, 12, 11, -4,
     0, 4, 6, 6, -7, -5, 4, 7, 1, -6, -3, -4, 2, 0, -18, 0, -8, -10, 4, -13,
     6, 0, -4, 8, -6, 0, 6, -12, 7, 1, 2, 18, 2, 6, -7, 12, 2, 5, 0, -12,
     3, 14, 4, -8, -11, -12, 12, -4, 12, -6, 6, 6, 5, 14, 4, -11, -4, 6, 1, 20,
     -12, 7, -6, 0, 4, -12, -20, -12, -18, 0, -6, -10, 6, -10, 12, 12, -1, -34, 2, -6] := by
  eta_coeff

end WeightTwoCusps
