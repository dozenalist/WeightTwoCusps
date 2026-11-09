module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«192».New.«192_eta_1m3_2p7_3p1_4m4_6m1_8p3_12p2_16m1_24m1_48p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 384

The eta expression is `η(2z)^(-3) η(4z)^7 η(6z) η(8z)^(-4) η(12z)^(-1) η(16z)^3 η(24z)^2 η(32z)^(-1) η(48z)^(-1) η(96z)`; see
[the local level table](../../TABLE.md#level-384).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_192_eta_1m3_2p7_3p1_4m4_6m1_8p3_12p2_16m1_24m1_48p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-3) η(4z)^7 η(6z) η(8z)^(-4) η(12z)^(-1) η(16z)^3 η(24z)^2 η(32z)^(-1) η(48z)^(-1) η(96z)` at level 384. -/
abbrev cuspForm_192_eta_1m3_2p7_3p1_4m4_6m1_8p3_12p2_16m1_24m1_48p1_old_384_2 : gamma0CuspForms 384 :=
  gamma0Rescale cuspForm_192_eta_1m3_2p7_3p1_4m4_6m1_8p3_12p2_16m1_24m1_48p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_192_eta_1m3_2p7_3p1_4m4_6m1_8p3_12p2_16m1_24m1_48p1_old_384_2_eq_eta :
    cuspForm_192_eta_1m3_2p7_3p1_4m4_6m1_8p3_12p2_16m1_24m1_48p1_old_384_2 =
      etaQuotientCuspForm 384 sparse![384; 1 => -3, 3 => 7, 5 => 1, 7 => -4, 11 => -1, 15 => 3, 23 => 2, 31 => -1, 47 => -1, 95 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_192_eta_1m3_2p7_3p1_4m4_6m1_8p3_12p2_16m1_24m1_48p1_old_384_2_first_coeffs :
    first_coeffs 100 cuspForm_192_eta_1m3_2p7_3p1_4m4_6m1_8p3_12p2_16m1_24m1_48p1_old_384_2 =
    [0, 0, 0, 0, 1, 0, 3, 0, 2, 0, 0, 0, 3, 0, 6, 0, 4, 0, 0, 0,
     2, 0, 6, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -6, 0,
     -4, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, -2, 0, -3, 0, 0, 0, 0, 0,
     -6, 0, -6, 0, 0, 0, 0, 0, -6, 0, -12, 0, 2, 0, 0, 0, 0, 0, -6, 0,
     -8, 0, 0, 0, -4, 0, 6, 0, -8, 0, 0, 0, 0, 0, -12, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
