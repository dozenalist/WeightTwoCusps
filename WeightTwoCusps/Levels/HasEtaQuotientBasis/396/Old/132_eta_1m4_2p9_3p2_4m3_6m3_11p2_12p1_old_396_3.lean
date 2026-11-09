module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«132».New.«132_eta_1m4_2p9_3p2_4m3_6m3_11p2_12p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 396

The eta expression is `η(3z)^(-4) η(6z)^9 η(9z)^2 η(12z)^(-3) η(18z)^(-3) η(33z)^2 η(36z)`; see
[the local level table](../../TABLE.md#level-396).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_132_eta_1m4_2p9_3p2_4m3_6m3_11p2_12p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-4) η(6z)^9 η(9z)^2 η(12z)^(-3) η(18z)^(-3) η(33z)^2 η(36z)` at level 396. -/
abbrev cuspForm_132_eta_1m4_2p9_3p2_4m3_6m3_11p2_12p1_old_396_3 : gamma0CuspForms 396 :=
  gamma0Rescale cuspForm_132_eta_1m4_2p9_3p2_4m3_6m3_11p2_12p1 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_132_eta_1m4_2p9_3p2_4m3_6m3_11p2_12p1_old_396_3_eq_eta :
    cuspForm_132_eta_1m4_2p9_3p2_4m3_6m3_11p2_12p1_old_396_3 =
      etaQuotientCuspForm 396 sparse![396; 2 => -4, 5 => 9, 8 => 2, 11 => -3, 17 => -3, 32 => 2, 35 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_132_eta_1m4_2p9_3p2_4m3_6m3_11p2_12p1_old_396_3_first_coeffs :
    first_coeffs 100 cuspForm_132_eta_1m4_2p9_3p2_4m3_6m3_11p2_12p1_old_396_3 =
    [0, 0, 0, 1, 0, 0, 4, 0, 0, 5, 0, 0, 2, 0, 0, 1, 0, 0, 2, 0,
     0, 4, 0, 0, 6, 0, 0, 4, 0, 0, 4, 0, 0, 1, 0, 0, -2, 0, 0, -2,
     0, 0, -8, 0, 0, -1, 0, 0, 2, 0, 0, -2, 0, 0, -2, 0, 0, -12, 0, 0,
     -4, 0, 0, -4, 0, 0, -2, 0, 0, 5, 0, 0, -12, 0, 0, -4, 0, 0, -8, 0,
     0, -7, 0, 0, 2, 0, 0, -12, 0, 0, -4, 0, 0, -11, 0, 0, -10, 0, 0, -1] := by
  eta_coeff

end WeightTwoCusps
