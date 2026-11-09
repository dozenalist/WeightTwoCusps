module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«192».New.«192_eta_1m4_2p11_3p2_4m3_6m4_12p1_24p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 384

The eta expression is `η(z)^(-4) η(2z)^11 η(3z)^2 η(4z)^(-3) η(6z)^(-4) η(12z) η(24z)`; see
[the local level table](../../TABLE.md#level-384).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_192_eta_1m4_2p11_3p2_4m3_6m4_12p1_24p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^11 η(3z)^2 η(4z)^(-3) η(6z)^(-4) η(12z) η(24z)` at level 384. -/
abbrev cuspForm_192_eta_1m4_2p11_3p2_4m3_6m4_12p1_24p1_old_384_1 : gamma0CuspForms 384 :=
  gamma0RescaleToLevel cuspForm_192_eta_1m4_2p11_3p2_4m3_6m4_12p1_24p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_192_eta_1m4_2p11_3p2_4m3_6m4_12p1_24p1_old_384_1_eq_eta :
    cuspForm_192_eta_1m4_2p11_3p2_4m3_6m4_12p1_24p1_old_384_1 =
      etaQuotientCuspForm 384 sparse![384; 0 => -4, 1 => 11, 2 => 2, 3 => -3, 5 => -4, 11 => 1, 23 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_192_eta_1m4_2p11_3p2_4m3_6m4_12p1_24p1_old_384_1_first_coeffs :
    first_coeffs 100 cuspForm_192_eta_1m4_2p11_3p2_4m3_6m4_12p1_24p1_old_384_1 =
    [0, 1, 4, 3, -6, -10, -6, 0, 12, 9, -8, -12, -6, 18, 24, 6, 0, -22, -12, 12,
     12, 12, -24, -24, -12, -1, 24, 3, 0, -26, -12, 24, 0, 12, 8, 0, -6, 2, 24, 6,
     -24, -14, 0, -12, 24, 6, 0, 0, 0, 41, -4, 6, 12, -2, -6, -24, 0, -12, -40, -12,
     12, -38, -24, 0, 0, 12, 0, 12, -12, 0, 48, 24, 12, -6, -8, -3, -24, 48, 12, -24,
     0, -15, 40, 12, 0, 28, -24, -18, 48, 10, 24, 0, -48, -12, -48, 24, 0, -78, -28, -12] := by
  eta_coeff

end WeightTwoCusps
