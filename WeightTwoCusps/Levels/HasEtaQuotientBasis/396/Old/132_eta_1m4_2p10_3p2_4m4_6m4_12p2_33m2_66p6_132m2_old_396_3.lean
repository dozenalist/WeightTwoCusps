module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«132».New.«132_eta_1m4_2p10_3p2_4m4_6m4_12p2_33m2_66p6_132m2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 396

The eta expression is `η(3z)^(-4) η(6z)^10 η(9z)^2 η(12z)^(-4) η(18z)^(-4) η(36z)^2 η(99z)^(-2) η(198z)^6 η(396z)^(-2)`; see
[the local level table](../../TABLE.md#level-396).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_132_eta_1m4_2p10_3p2_4m4_6m4_12p2_33m2_66p6_132m2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-4) η(6z)^10 η(9z)^2 η(12z)^(-4) η(18z)^(-4) η(36z)^2 η(99z)^(-2) η(198z)^6 η(396z)^(-2)` at level 396. -/
abbrev cuspForm_132_eta_1m4_2p10_3p2_4m4_6m4_12p2_33m2_66p6_132m2_old_396_3 : gamma0CuspForms 396 :=
  gamma0Rescale cuspForm_132_eta_1m4_2p10_3p2_4m4_6m4_12p2_33m2_66p6_132m2 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_132_eta_1m4_2p10_3p2_4m4_6m4_12p2_33m2_66p6_132m2_old_396_3_eq_eta :
    cuspForm_132_eta_1m4_2p10_3p2_4m4_6m4_12p2_33m2_66p6_132m2_old_396_3 =
      etaQuotientCuspForm 396 sparse![396; 2 => -4, 5 => 10, 8 => 2, 11 => -4, 17 => -4, 35 => 2, 98 => -2, 197 => 6, 395 => -2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_132_eta_1m4_2p10_3p2_4m4_6m4_12p2_33m2_66p6_132m2_old_396_3_first_coeffs :
    first_coeffs 100 cuspForm_132_eta_1m4_2p10_3p2_4m4_6m4_12p2_33m2_66p6_132m2_old_396_3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 4, 0, 0, 4, 0, 0, -2, 0,
     0, -4, 0, 0, 0, 0, 0, 3, 0, 0, 4, 0, 0, 0, 0, 0, -2, 0, 0, -4,
     0, 0, -8, 0, 0, 1, 0, 0, 4, 0, 0, 0, 0, 0, -2, 0, 0, -8, 0, 0,
     0, 0, 0, 2, 0, 0, 0, 0, 0, 4, 0, 0, -4, 0, 0, -4, 0, 0, 0, 0,
     0, 2, 0, 0, 4, 0, 0, 0, 0, 0, -2, 0, 0, -4, 0, 0, -8, 0, 0, 1] := by
  eta_coeff

end WeightTwoCusps
