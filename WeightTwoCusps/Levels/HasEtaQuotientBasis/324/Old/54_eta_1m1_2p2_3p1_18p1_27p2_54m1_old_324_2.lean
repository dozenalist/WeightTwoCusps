module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«54».New.«54_eta_1m1_2p2_3p1_18p1_27p2_54m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 324

The eta expression is `η(2z)^(-1) η(4z)^2 η(6z) η(36z) η(54z)^2 η(108z)^(-1)`; see
[the local level table](../../TABLE.md#level-324).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-1) η(4z)^2 η(6z) η(36z) η(54z)^2 η(108z)^(-1)` at level 324. -/
abbrev cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_324_2 : gamma0CuspForms 324 :=
  gamma0RescaleToLevel cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_324_2_eq_eta :
    cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_324_2 =
      etaQuotientCuspForm 324 sparse![324; 1 => -1, 3 => 2, 5 => 1, 35 => 1, 53 => 2, 107 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_324_2_first_coeffs :
    first_coeffs 100 cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_324_2 =
    [0, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, -1, 0, 0, 0,
     -2, 0, 1, 0, 0, 0, -1, 0, -1, 0, 0, 0, 2, 0, 0, 0, 0, 0, -1, 0,
     -1, 0, 0, 0, 2, 0, 2, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, -2, 0,
     0, 0, 2, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 5, 0, -4, 0, 0, 0,
     -2, 0, 2, 0, 0, 0, -4, 0, 1, 0, 0, 0, 4, 0, -2, 0, 0, 0, -6, 0] := by
  eta_coeff

end WeightTwoCusps
