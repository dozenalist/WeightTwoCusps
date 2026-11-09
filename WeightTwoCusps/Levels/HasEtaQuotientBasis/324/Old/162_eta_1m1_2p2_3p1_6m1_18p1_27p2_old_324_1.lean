module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«162».New.«162_eta_1m1_2p2_3p1_6m1_18p1_27p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 324

The eta expression is `η(z)^(-1) η(2z)^2 η(3z) η(6z)^(-1) η(18z) η(27z)^2`; see
[the local level table](../../TABLE.md#level-324).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_162_eta_1m1_2p2_3p1_6m1_18p1_27p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(3z) η(6z)^(-1) η(18z) η(27z)^2` at level 324. -/
abbrev cuspForm_162_eta_1m1_2p2_3p1_6m1_18p1_27p2_old_324_1 : gamma0CuspForms 324 :=
  gamma0RescaleToLevel cuspForm_162_eta_1m1_2p2_3p1_6m1_18p1_27p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_162_eta_1m1_2p2_3p1_6m1_18p1_27p2_old_324_1_eq_eta :
    cuspForm_162_eta_1m1_2p2_3p1_6m1_18p1_27p2_old_324_1 =
      etaQuotientCuspForm 324 sparse![324; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 17 => 1, 26 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_162_eta_1m1_2p2_3p1_6m1_18p1_27p2_old_324_1_first_coeffs :
    first_coeffs 100 cuspForm_162_eta_1m1_2p2_3p1_6m1_18p1_27p2_old_324_1 =
    [0, 0, 0, 1, 1, 0, 0, -1, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, -1,
     0, -1, -1, 0, 0, 1, 0, 0, 1, 0, 0, -2, 0, 0, 2, 0, 0, 1, 0, 5,
     -1, 0, 0, 1, 0, 0, 1, 0, 4, 2, 0, 0, -1, 0, 0, -1, 0, -7, -1, 0,
     0, 1, 0, 0, -3, 0, 0, 1, 0, 0, -3, 0, 0, 3, 0, -5, 1, 0, 0, -3,
     0, 0, -3, 0, 2, 3, 0, 0, -3, 0, 0, 1, 0, -4, 4, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
