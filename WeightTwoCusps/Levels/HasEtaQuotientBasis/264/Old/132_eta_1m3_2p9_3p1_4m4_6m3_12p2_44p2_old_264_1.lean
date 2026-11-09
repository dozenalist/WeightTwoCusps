module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«132».New.«132_eta_1m3_2p9_3p1_4m4_6m3_12p2_44p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-3) η(2z)^9 η(3z) η(4z)^(-4) η(6z)^(-3) η(12z)^2 η(44z)^2`; see
[the local level table](../../TABLE.md#level-264).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_132_eta_1m3_2p9_3p1_4m4_6m3_12p2_44p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^9 η(3z) η(4z)^(-4) η(6z)^(-3) η(12z)^2 η(44z)^2` at level 264. -/
abbrev cuspForm_132_eta_1m3_2p9_3p1_4m4_6m3_12p2_44p2_old_264_1 : gamma0CuspForms 264 :=
  gamma0RescaleToLevel cuspForm_132_eta_1m3_2p9_3p1_4m4_6m3_12p2_44p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_132_eta_1m3_2p9_3p1_4m4_6m3_12p2_44p2_old_264_1_eq_eta :
    cuspForm_132_eta_1m3_2p9_3p1_4m4_6m3_12p2_44p2_old_264_1 =
      etaQuotientCuspForm 264 sparse![264; 0 => -3, 1 => 9, 2 => 1, 3 => -4, 5 => -3, 11 => 2, 43 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_132_eta_1m3_2p9_3p1_4m4_6m3_12p2_44p2_old_264_1_first_coeffs :
    first_coeffs 100 cuspForm_132_eta_1m3_2p9_3p1_4m4_6m3_12p2_44p2_old_264_1 =
    [0, 0, 0, 0, 1, 3, 0, -6, -2, 3, 0, 0, -1, 0, 0, -6, 2, 6, 0, 0,
     1, 6, 0, -6, 2, 3, 0, 0, -2, 0, 0, -6, 0, 0, 0, 0, -2, 9, 0, -6,
     -2, 0, 0, 0, 1, 0, 0, -12, -2, 0, 0, 12, 4, 0, 0, 0, 4, 6, 0, 12,
     -1, -12, 0, -6, -4, -12, 0, 12, -2, -3, 0, -6, 4, 6, 0, 12, 0, 0, 0, -6,
     2, -12, 0, 12, 2, 6, 0, -12, -2, 3, 0, 24, -1, -15, 0, 0, 0, -15, 0, 0] := by
  eta_coeff

end WeightTwoCusps
