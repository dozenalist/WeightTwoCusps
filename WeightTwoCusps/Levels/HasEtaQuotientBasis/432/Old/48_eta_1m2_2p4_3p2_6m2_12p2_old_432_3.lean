module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«48».New.«48_eta_1m2_2p4_3p2_6m2_12p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 432

The eta expression is `η(3z)^(-2) η(6z)^4 η(9z)^2 η(18z)^(-2) η(36z)^2`; see
[the local level table](../../TABLE.md#level-432).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-2) η(6z)^4 η(9z)^2 η(18z)^(-2) η(36z)^2` at level 432. -/
abbrev cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_432_3 : gamma0CuspForms 432 :=
  gamma0RescaleToLevel cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2 3 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_432_3_eq_eta :
    cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_432_3 =
      etaQuotientCuspForm 432 sparse![432; 2 => -2, 5 => 4, 8 => 2, 17 => -2, 35 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_432_3_first_coeffs :
    first_coeffs 100 cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_old_432_3 =
    [0, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, -2, 0, 0, -2, 0,
     0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -4, 0, 0, -4, 0, 0, 0, 0, 0, -2,
     0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 4, 0, 0,
     0, 0, 0, 0, 0, 0, 8, 0, 0, 8, 0, 0, 0, 0, 0, -1, 0, 0, -4, 0,
     0, 1, 0, 0, 0, 0, 0, 6, 0, 0, 4, 0, 0, -8, 0, 0, 0, 0, 0, -4] := by
  eta_coeff

end WeightTwoCusps
