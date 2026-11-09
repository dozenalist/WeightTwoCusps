module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«132».New.«132_eta_1m2_2p2_3p4_6m2_11p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^4 η(6z)^(-2) η(11z)^2`; see
[the local level table](../../TABLE.md#level-264).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_132_eta_1m2_2p2_3p4_6m2_11p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^4 η(6z)^(-2) η(11z)^2` at level 264. -/
abbrev cuspForm_132_eta_1m2_2p2_3p4_6m2_11p2_old_264_1 : gamma0CuspForms 264 :=
  gamma0RescaleToLevel cuspForm_132_eta_1m2_2p2_3p4_6m2_11p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_132_eta_1m2_2p2_3p4_6m2_11p2_old_264_1_eq_eta :
    cuspForm_132_eta_1m2_2p2_3p4_6m2_11p2_old_264_1 =
      etaQuotientCuspForm 264 sparse![264; 0 => -2, 1 => 2, 2 => 4, 5 => -2, 10 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_132_eta_1m2_2p2_3p4_6m2_11p2_old_264_1_first_coeffs :
    first_coeffs 100 cuspForm_132_eta_1m2_2p2_3p4_6m2_11p2_old_264_1 =
    [0, 1, 2, 3, 2, 1, 2, 2, 4, 2, 2, 1, -2, 0, -4, -1, 0, -2, 0, -8,
     -2, -2, -2, 3, -8, -4, -8, -3, 0, -8, -2, -5, -4, -1, -4, -2, 0, 3, 0, -8,
     -4, 8, 4, 2, 2, -6, 6, 0, 8, -3, -4, 10, -4, 2, -2, 1, 8, 8, 16, 1,
     2, 16, 10, 8, -4, 4, 2, 5, 4, -3, -4, 9, 12, 4, -6, 0, 8, -2, 8, 2,
     4, -3, 0, 10, -8, 6, 12, 0, 0, -17, 0, -8, 10, 13, -20, -8, 0, 9, 2, -2] := by
  eta_coeff

end WeightTwoCusps
