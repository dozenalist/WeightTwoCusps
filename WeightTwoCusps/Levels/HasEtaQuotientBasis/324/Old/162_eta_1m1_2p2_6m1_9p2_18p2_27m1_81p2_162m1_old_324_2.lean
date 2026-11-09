module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«162».New.«162_eta_1m1_2p2_6m1_9p2_18p2_27m1_81p2_162m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 324

The eta expression is `η(2z)^(-1) η(4z)^2 η(12z)^(-1) η(18z)^2 η(36z)^2 η(54z)^(-1) η(162z)^2 η(324z)^(-1)`; see
[the local level table](../../TABLE.md#level-324).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_162_eta_1m1_2p2_6m1_9p2_18p2_27m1_81p2_162m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-1) η(4z)^2 η(12z)^(-1) η(18z)^2 η(36z)^2 η(54z)^(-1) η(162z)^2 η(324z)^(-1)` at level 324. -/
abbrev cuspForm_162_eta_1m1_2p2_6m1_9p2_18p2_27m1_81p2_162m1_old_324_2 : gamma0CuspForms 324 :=
  gamma0Rescale cuspForm_162_eta_1m1_2p2_6m1_9p2_18p2_27m1_81p2_162m1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_162_eta_1m1_2p2_6m1_9p2_18p2_27m1_81p2_162m1_old_324_2_eq_eta :
    cuspForm_162_eta_1m1_2p2_6m1_9p2_18p2_27m1_81p2_162m1_old_324_2 =
      etaQuotientCuspForm 324 sparse![324; 1 => -1, 3 => 2, 11 => -1, 17 => 2, 35 => 2, 53 => -1, 161 => 2, 323 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_162_eta_1m1_2p2_6m1_9p2_18p2_27m1_81p2_162m1_old_324_2_first_coeffs :
    first_coeffs 100 cuspForm_162_eta_1m1_2p2_6m1_9p2_18p2_27m1_81p2_162m1_old_324_2 =
    [0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0,
     -1, 0, -1, 0, 0, 0, 1, 0, 2, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0,
     -2, 0, 0, 0, -4, 0, -2, 0, 0, 0, -4, 0, 0, 0, 0, 0, 2, 0, 2, 0,
     0, 0, 0, 0, -3, 0, 0, 0, 1, 0, 0, 0, 0, 0, -5, 0, 1, 0, 0, 0,
     1, 0, 3, 0, 0, 0, 0, 0, -5, 0, 0, 0, -2, 0, -2, 0, 0, 0, -3, 0] := by
  eta_coeff

end WeightTwoCusps
