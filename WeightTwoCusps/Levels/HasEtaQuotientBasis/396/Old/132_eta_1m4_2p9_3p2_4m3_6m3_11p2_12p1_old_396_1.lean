module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«132».New.«132_eta_1m4_2p9_3p2_4m3_6m3_11p2_12p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 396

The eta expression is `η(z)^(-4) η(2z)^9 η(3z)^2 η(4z)^(-3) η(6z)^(-3) η(11z)^2 η(12z)`; see
[the local level table](../../TABLE.md#level-396).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_132_eta_1m4_2p9_3p2_4m3_6m3_11p2_12p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^9 η(3z)^2 η(4z)^(-3) η(6z)^(-3) η(11z)^2 η(12z)` at level 396. -/
abbrev cuspForm_132_eta_1m4_2p9_3p2_4m3_6m3_11p2_12p1_old_396_1 : gamma0CuspForms 396 :=
  gamma0RescaleToLevel cuspForm_132_eta_1m4_2p9_3p2_4m3_6m3_11p2_12p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_132_eta_1m4_2p9_3p2_4m3_6m3_11p2_12p1_old_396_1_eq_eta :
    cuspForm_132_eta_1m4_2p9_3p2_4m3_6m3_11p2_12p1_old_396_1 =
      etaQuotientCuspForm 396 sparse![396; 0 => -4, 1 => 9, 2 => 2, 3 => -3, 5 => -3, 10 => 2, 11 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_132_eta_1m4_2p9_3p2_4m3_6m3_11p2_12p1_old_396_1_first_coeffs :
    first_coeffs 100 cuspForm_132_eta_1m4_2p9_3p2_4m3_6m3_11p2_12p1_old_396_1 =
    [0, 1, 4, 5, 2, 1, 2, 4, 6, 4, 4, 1, -2, -2, -8, -1, 2, -2, -2, -12,
     -4, -4, -2, 5, -12, -4, -8, -7, 2, -12, -4, -11, -10, -1, -8, -2, 2, 3, 0, -10,
     -6, 16, 8, 6, 2, -8, 8, -4, 10, -3, -10, 14, -10, 6, 2, 1, 12, 12, 24, -1,
     4, 18, 22, 10, -2, 4, 2, 11, 8, -5, -8, 15, 18, 4, -6, -2, 12, -2, 8, 8,
     8, -5, -8, 18, -14, 10, 12, 0, 0, -33, -2, -8, 16, 23, -22, -12, 4, 17, 0, -2] := by
  eta_coeff

end WeightTwoCusps
