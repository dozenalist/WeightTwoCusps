module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«54».New.«54_eta_1m1_2p2_3p1_18p1_27p2_54m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 324

The eta expression is `η(6z)^(-1) η(12z)^2 η(18z) η(108z) η(162z)^2 η(324z)^(-1)`; see
[the local level table](../../TABLE.md#level-324).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(6z)` of `cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z)^(-1) η(12z)^2 η(18z) η(108z) η(162z)^2 η(324z)^(-1)` at level 324. -/
abbrev cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_324_6 : gamma0CuspForms 324 :=
  gamma0Rescale cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1 6

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_324_6_eq_eta :
    cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_324_6 =
      etaQuotientCuspForm 324 sparse![324; 5 => -1, 11 => 2, 17 => 1, 107 => 1, 161 => 2, 323 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_324_6_first_coeffs :
    first_coeffs 100 cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_324_6 =
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     -2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0,
     0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
