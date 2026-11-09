module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«192».New.«192_eta_1m3_2p9_3p1_4m3_6m3_12p1_24p1_32p2_64m1_96m1_192p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 384

The eta expression is `η(2z)^(-3) η(4z)^9 η(6z) η(8z)^(-3) η(12z)^(-3) η(24z) η(48z) η(64z)^2 η(128z)^(-1) η(192z)^(-1) η(384z)`; see
[the local level table](../../TABLE.md#level-384).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_192_eta_1m3_2p9_3p1_4m3_6m3_12p1_24p1_32p2_64m1_96m1_192p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-3) η(4z)^9 η(6z) η(8z)^(-3) η(12z)^(-3) η(24z) η(48z) η(64z)^2 η(128z)^(-1) η(192z)^(-1) η(384z)` at level 384. -/
abbrev cuspForm_192_eta_1m3_2p9_3p1_4m3_6m3_12p1_24p1_32p2_64m1_96m1_192p1_old_384_2 : gamma0CuspForms 384 :=
  gamma0Rescale cuspForm_192_eta_1m3_2p9_3p1_4m3_6m3_12p1_24p1_32p2_64m1_96m1_192p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_192_eta_1m3_2p9_3p1_4m3_6m3_12p1_24p1_32p2_64m1_96m1_192p1_old_384_2_eq_eta :
    cuspForm_192_eta_1m3_2p9_3p1_4m3_6m3_12p1_24p1_32p2_64m1_96m1_192p1_old_384_2 =
      etaQuotientCuspForm 384 sparse![384; 1 => -3, 3 => 9, 5 => 1, 7 => -3, 11 => -3, 23 => 1, 47 => 1, 63 => 2, 127 => -1, 191 => -1, 383 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_192_eta_1m3_2p9_3p1_4m3_6m3_12p1_24p1_32p2_64m1_96m1_192p1_old_384_2_first_coeffs :
    first_coeffs 100 cuspForm_192_eta_1m3_2p9_3p1_4m3_6m3_12p1_24p1_32p2_64m1_96m1_192p1_old_384_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 0, -6, 0, -3, 0,
     0, 0, 0, 0, 6, 0, 0, 0, -6, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0,
     0, 0, -3, 0, 0, 0, 0, 0, 6, 0, 0, 0, -12, 0, 0, 0, 0, 0, -1, 0,
     0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0,
     12, 0, 6, 0, 0, 0, 0, 0, -24, 0, 3, 0, 12, 0, 0, 0, 0, 0, -12, 0] := by
  eta_coeff

end WeightTwoCusps
