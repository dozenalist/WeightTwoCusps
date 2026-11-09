module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«42».New.«42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 336

The eta expression is `η(4z)^(-1) η(8z) η(12z)^4 η(24z)^(-2) η(28z) η(56z)^(-1) η(84z)^(-2) η(168z)^4`; see
[the local level table](../../TABLE.md#level-336).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^(-1) η(8z) η(12z)^4 η(24z)^(-2) η(28z) η(56z)^(-1) η(84z)^(-2) η(168z)^4` at level 336. -/
abbrev cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_336_4 : gamma0CuspForms 336 :=
  gamma0RescaleToLevel cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4 4 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_336_4_eq_eta :
    cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_336_4 =
      etaQuotientCuspForm 336 sparse![336; 3 => -1, 7 => 1, 11 => 4, 23 => -2, 27 => 1, 55 => -1, 83 => -2, 167 => 4] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_336_4_first_coeffs :
    first_coeffs 100 cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_336_4 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, -2, 0, 0, 0, -2, 0, 0, 0,
     -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, -1, 0, 0, 0,
     0, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, -2, 0, 0, 0, -1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
