module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«132».New.«132_eta_1m4_2p10_3p2_4m4_6m4_12p2_33m2_66p6_132m2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 396

The eta expression is `η(z)^(-4) η(2z)^10 η(3z)^2 η(4z)^(-4) η(6z)^(-4) η(12z)^2 η(33z)^(-2) η(66z)^6 η(132z)^(-2)`; see
[the local level table](../../TABLE.md#level-396).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_132_eta_1m4_2p10_3p2_4m4_6m4_12p2_33m2_66p6_132m2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^10 η(3z)^2 η(4z)^(-4) η(6z)^(-4) η(12z)^2 η(33z)^(-2) η(66z)^6 η(132z)^(-2)` at level 396. -/
abbrev cuspForm_132_eta_1m4_2p10_3p2_4m4_6m4_12p2_33m2_66p6_132m2_old_396_1 : gamma0CuspForms 396 :=
  gamma0RescaleToLevel cuspForm_132_eta_1m4_2p10_3p2_4m4_6m4_12p2_33m2_66p6_132m2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_132_eta_1m4_2p10_3p2_4m4_6m4_12p2_33m2_66p6_132m2_old_396_1_eq_eta :
    cuspForm_132_eta_1m4_2p10_3p2_4m4_6m4_12p2_33m2_66p6_132m2_old_396_1 =
      etaQuotientCuspForm 396 sparse![396; 0 => -4, 1 => 10, 2 => 2, 3 => -4, 5 => -4, 11 => 2, 32 => -2, 65 => 6, 131 => -2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_132_eta_1m4_2p10_3p2_4m4_6m4_12p2_33m2_66p6_132m2_old_396_1_first_coeffs :
    first_coeffs 100 cuspForm_132_eta_1m4_2p10_3p2_4m4_6m4_12p2_33m2_66p6_132m2_old_396_1 =
    [0, 0, 0, 1, 4, 4, -2, -4, 0, 3, 4, 0, -2, -4, -8, 1, 4, 0, -2, -8,
     0, 2, 0, 4, -4, -4, 0, 2, 4, 0, -2, -4, -8, 1, 8, 0, 2, 4, 8, 0,
     -4, 8, 4, 8, 0, -1, -4, -16, 0, 0, 0, -2, -12, 0, 0, 0, 8, -8, 0, 12,
     2, 4, 0, -2, -4, -16, 2, 12, -8, 3, -8, -4, 8, 8, 16, -4, 0, 0, 8, 4,
     8, -3, -16, 0, 0, 16, -8, -8, 0, -4, 2, 16, 24, -5, -4, 8, 4, 4, 8, -1] := by
  eta_coeff

end WeightTwoCusps
