module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«42».New.«42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 336

The eta expression is `η(4z)^(-2) η(8z)^4 η(12z) η(24z)^(-1) η(28z)^4 η(56z)^(-2) η(84z)^(-1) η(168z)`; see
[the local level table](../../TABLE.md#level-336).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^(-2) η(8z)^4 η(12z) η(24z)^(-1) η(28z)^4 η(56z)^(-2) η(84z)^(-1) η(168z)` at level 336. -/
abbrev cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_336_4 : gamma0CuspForms 336 :=
  gamma0RescaleToLevel cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1 4 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_336_4_eq_eta :
    cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_336_4 =
      etaQuotientCuspForm 336 sparse![336; 3 => -2, 7 => 4, 11 => 1, 23 => -1, 27 => 4, 55 => -2, 83 => -1, 167 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_336_4_first_coeffs :
    first_coeffs 100 cuspForm_42_eta_1m2_2p4_3p1_6m1_7p4_14m2_21m1_42p1_old_336_4 =
    [0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0,
     0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, -4, 0, 0, 0, -8, 0, 0, 0,
     -6, 0, 0, 0, -6, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, -4, 0, 0, 0,
     3, 0, 0, 0, 7, 0, 0, 0, 12, 0, 0, 0, 11, 0, 0, 0, -4, 0, 0, 0,
     0, 0, 0, 0, 4, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, -7, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
