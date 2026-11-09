module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«42».New.«42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(5z)^(-2) η(10z)^4 η(15z) η(30z)^(-1) η(35z)^4 η(70z)^(-2) η(105z)^(-1) η(210z)`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(5z)` of `cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(5z)^(-2) η(10z)^4 η(15z) η(30z)^(-1) η(35z)^4 η(70z)^(-2) η(105z)^(-1) η(210z)` at level 420. -/
abbrev cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_420_5 : gamma0CuspForms 420 :=
  gamma0RescaleToLevel cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1 5 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_420_5_eq_eta :
    cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_420_5 =
      etaQuotientCuspForm 420 sparse![420; 4 => -2, 9 => 4, 14 => 1, 29 => -1, 34 => 4, 69 => -2, 104 => -1, 209 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_420_5_first_coeffs :
    first_coeffs 100 cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_420_5 =
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0,
     -4, 0, 0, 0, 0, -8, 0, 0, 0, 0, -6, 0, 0, 0, 0, -6, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 2, 0, 0, 0, 0, -4, 0, 0, 0, 0, 3, 0, 0, 0, 0,
     7, 0, 0, 0, 0, 12, 0, 0, 0, 0, 11, 0, 0, 0, 0, -4, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
