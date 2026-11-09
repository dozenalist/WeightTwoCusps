module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«42».New.«42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 126

The eta expression is `η(3z)^(-1) η(6z) η(9z)^4 η(18z)^(-2) η(21z) η(42z)^(-1) η(63z)^(-2) η(126z)^4`; see
[the local level table](../../TABLE.md#level-126).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-1) η(6z) η(9z)^4 η(18z)^(-2) η(21z) η(42z)^(-1) η(63z)^(-2) η(126z)^4` at level 126. -/
abbrev cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_126_3 : gamma0CuspForms 126 :=
  gamma0Rescale cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_126_3_eq_eta :
    cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_126_3 =
      etaQuotientCuspForm 126 sparse![126; 2 => -1, 5 => 1, 8 => 4, 17 => -2, 20 => 1, 41 => -1, 62 => -2, 125 => 4] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_126_3_first_coeffs :
    first_coeffs 100 cuspForm_42_eta_1m1_2p1_3p4_6m2_7p1_14m1_21m2_42p4_old_126_3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0,
     0, 1, 0, 0, -2, 0, 0, -2, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -3,
     0, 0, -1, 0, 0, 0, 0, 0, 2, 0, 0, 4, 0, 0, 2, 0, 0, 1, 0, 0,
     1, 0, 0, 0, 0, 0, 4, 0, 0, -2, 0, 0, -1, 0, 0, -2, 0, 0, -1, 0,
     0, 3, 0, 0, 1, 0, 0, -2, 0, 0, -2, 0, 0, -2, 0, 0, 0, 0, 0, -2] := by
  eta_coeff

end WeightTwoCusps
