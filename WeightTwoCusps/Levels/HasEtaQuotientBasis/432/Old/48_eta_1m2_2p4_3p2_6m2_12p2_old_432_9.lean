module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«48».New.«48_eta_1m2_2p4_3p2_6m2_12p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 432

The eta expression is `η(9z)^(-2) η(18z)^4 η(27z)^2 η(54z)^(-2) η(108z)^2`; see
[the local level table](../../TABLE.md#level-432).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(9z)` of `cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(9z)^(-2) η(18z)^4 η(27z)^2 η(54z)^(-2) η(108z)^2` at level 432. -/
abbrev cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_432_9 : gamma0CuspForms 432 :=
  gamma0Rescale cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2 9

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_432_9_eq_eta :
    cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_432_9 =
      etaQuotientCuspForm 432 sparse![432; 8 => -2, 17 => 4, 26 => 2, 53 => -2, 107 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_432_9_first_coeffs :
    first_coeffs 100 cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_432_9 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0,
     0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, -4] := by
  eta_coeff

end WeightTwoCusps
