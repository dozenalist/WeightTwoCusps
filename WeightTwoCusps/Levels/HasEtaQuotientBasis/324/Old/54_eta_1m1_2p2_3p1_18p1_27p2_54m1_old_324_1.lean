module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«54».New.«54_eta_1m1_2p2_3p1_18p1_27p2_54m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 324

The eta expression is `η(z)^(-1) η(2z)^2 η(3z) η(18z) η(27z)^2 η(54z)^(-1)`; see
[the local level table](../../TABLE.md#level-324).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(3z) η(18z) η(27z)^2 η(54z)^(-1)` at level 324. -/
abbrev cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_324_1 : gamma0CuspForms 324 :=
  gamma0RescaleToLevel cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_324_1_eq_eta :
    cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_324_1 =
      etaQuotientCuspForm 324 sparse![324; 0 => -1, 1 => 2, 2 => 1, 17 => 1, 26 => 2, 53 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_324_1_first_coeffs :
    first_coeffs 100 cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_324_1 =
    [0, 1, 1, 0, 0, -1, 0, -1, -1, 0, -2, 1, 0, -1, -1, 0, 2, 0, 0, -1,
     -1, 0, 2, 2, 0, 1, 2, 0, 0, -2, 0, 2, 3, 0, 0, 1, 0, 5, -4, 0,
     -2, 2, 0, -4, 1, 0, 4, -2, 0, -6, -2, 0, -6, -3, 0, -6, 1, 0, -4, -4,
     0, 5, -1, 0, -2, 4, 0, 11, 0, 0, 2, 0, 0, -7, 8, 0, 6, -1, 0, 11,
     -1, 0, 4, 1, 0, 0, 2, 0, 2, 6, 0, 1, 2, 0, -4, -2, 0, -7, -6, 0] := by
  eta_coeff

end WeightTwoCusps
