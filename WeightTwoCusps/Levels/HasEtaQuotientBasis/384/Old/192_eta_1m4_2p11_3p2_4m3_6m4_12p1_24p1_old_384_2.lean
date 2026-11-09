module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«192».New.«192_eta_1m4_2p11_3p2_4m3_6m4_12p1_24p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 384

The eta expression is `η(2z)^(-4) η(4z)^11 η(6z)^2 η(8z)^(-3) η(12z)^(-4) η(24z) η(48z)`; see
[the local level table](../../TABLE.md#level-384).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_192_eta_1m4_2p11_3p2_4m3_6m4_12p1_24p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-4) η(4z)^11 η(6z)^2 η(8z)^(-3) η(12z)^(-4) η(24z) η(48z)` at level 384. -/
abbrev cuspForm_192_eta_1m4_2p11_3p2_4m3_6m4_12p1_24p1_old_384_2 : gamma0CuspForms 384 :=
  gamma0Rescale cuspForm_192_eta_1m4_2p11_3p2_4m3_6m4_12p1_24p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_192_eta_1m4_2p11_3p2_4m3_6m4_12p1_24p1_old_384_2_eq_eta :
    cuspForm_192_eta_1m4_2p11_3p2_4m3_6m4_12p1_24p1_old_384_2 =
      etaQuotientCuspForm 384 sparse![384; 1 => -4, 3 => 11, 5 => 2, 7 => -3, 11 => -4, 23 => 1, 47 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_192_eta_1m4_2p11_3p2_4m3_6m4_12p1_24p1_old_384_2_first_coeffs :
    first_coeffs 100 cuspForm_192_eta_1m4_2p11_3p2_4m3_6m4_12p1_24p1_old_384_2 =
    [0, 0, 1, 0, 4, 0, 3, 0, -6, 0, -10, 0, -6, 0, 0, 0, 12, 0, 9, 0,
     -8, 0, -12, 0, -6, 0, 18, 0, 24, 0, 6, 0, 0, 0, -22, 0, -12, 0, 12, 0,
     12, 0, 12, 0, -24, 0, -24, 0, -12, 0, -1, 0, 24, 0, 3, 0, 0, 0, -26, 0,
     -12, 0, 24, 0, 0, 0, 12, 0, 8, 0, 0, 0, -6, 0, 2, 0, 24, 0, 6, 0,
     -24, 0, -14, 0, 0, 0, -12, 0, 24, 0, 6, 0, 0, 0, 0, 0, 0, 0, 41, 0] := by
  eta_coeff

end WeightTwoCusps
