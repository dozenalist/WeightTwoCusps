module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«192».New.«192_eta_1m4_2p9_3p2_4m4_6m2_8p1_12p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 384

The eta expression is `η(z)^(-4) η(2z)^9 η(3z)^2 η(4z)^(-4) η(6z)^(-2) η(8z) η(12z)^2`; see
[the local level table](../../TABLE.md#level-384).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_192_eta_1m4_2p9_3p2_4m4_6m2_8p1_12p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^9 η(3z)^2 η(4z)^(-4) η(6z)^(-2) η(8z) η(12z)^2` at level 384. -/
abbrev cuspForm_192_eta_1m4_2p9_3p2_4m4_6m2_8p1_12p2_old_384_1 : gamma0CuspForms 384 :=
  gamma0RescaleToLevel cuspForm_192_eta_1m4_2p9_3p2_4m4_6m2_8p1_12p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_192_eta_1m4_2p9_3p2_4m4_6m2_8p1_12p2_old_384_1_eq_eta :
    cuspForm_192_eta_1m4_2p9_3p2_4m4_6m2_8p1_12p2_old_384_1 =
      etaQuotientCuspForm 384 sparse![384; 0 => -4, 1 => 9, 2 => 2, 3 => -4, 5 => -2, 7 => 1, 11 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_192_eta_1m4_2p9_3p2_4m4_6m2_8p1_12p2_old_384_1_first_coeffs :
    first_coeffs 100 cuspForm_192_eta_1m4_2p9_3p2_4m4_6m2_8p1_12p2_old_384_1 =
    [0, 1, 4, 5, 2, 2, 6, 8, 4, 1, 8, 8, 2, 2, 0, 2, 0, 2, 4, -8,
     -4, 0, 0, 0, -4, -1, -8, -7, 0, -6, -12, -8, 0, -4, -24, -16, 2, -6, 0, -14,
     -8, -6, -16, 8, -8, 2, 0, -16, 0, -7, -4, -6, -4, 2, -18, -16, 0, 4, 8, -8,
     -4, 2, 0, 8, 0, 4, 16, 8, 4, -8, 0, 32, 4, 10, -8, -5, 8, 0, 36, -8,
     0, 1, 8, 24, 0, 4, 0, 26, 16, -6, 8, 16, 16, 8, 0, 16, 0, 2, 36, 8] := by
  eta_coeff

end WeightTwoCusps
