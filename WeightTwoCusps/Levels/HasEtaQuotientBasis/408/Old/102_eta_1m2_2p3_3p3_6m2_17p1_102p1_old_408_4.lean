module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«102».New.«102_eta_1m2_2p3_3p3_6m2_17p1_102p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 408

The eta expression is `η(4z)^(-2) η(8z)^3 η(12z)^3 η(24z)^(-2) η(68z) η(408z)`; see
[the local level table](../../TABLE.md#level-408).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_102_eta_1m2_2p3_3p3_6m2_17p1_102p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^(-2) η(8z)^3 η(12z)^3 η(24z)^(-2) η(68z) η(408z)` at level 408. -/
abbrev cuspForm_102_eta_1m2_2p3_3p3_6m2_17p1_102p1_old_408_4 : gamma0CuspForms 408 :=
  gamma0Rescale cuspForm_102_eta_1m2_2p3_3p3_6m2_17p1_102p1 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_102_eta_1m2_2p3_3p3_6m2_17p1_102p1_old_408_4_eq_eta :
    cuspForm_102_eta_1m2_2p3_3p3_6m2_17p1_102p1_old_408_4 =
      etaQuotientCuspForm 408 sparse![408; 3 => -2, 7 => 3, 11 => 3, 23 => -2, 67 => 1, 407 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_102_eta_1m2_2p3_3p3_6m2_17p1_102p1_old_408_4_first_coeffs :
    first_coeffs 100 cuspForm_102_eta_1m2_2p3_3p3_6m2_17p1_102p1_old_408_4 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, -3, 0, 0, 0,
     -2, 0, 0, 0, -3, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, -2, 0, 0, 0,
     1, 0, 0, 0, -3, 0, 0, 0, -2, 0, 0, 0, -3, 0, 0, 0, -3, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
