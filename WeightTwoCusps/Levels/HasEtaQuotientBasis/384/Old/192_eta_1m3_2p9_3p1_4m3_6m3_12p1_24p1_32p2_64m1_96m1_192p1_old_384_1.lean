module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«192».New.«192_eta_1m3_2p9_3p1_4m3_6m3_12p1_24p1_32p2_64m1_96m1_192p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 384

The eta expression is `η(z)^(-3) η(2z)^9 η(3z) η(4z)^(-3) η(6z)^(-3) η(12z) η(24z) η(32z)^2 η(64z)^(-1) η(96z)^(-1) η(192z)`; see
[the local level table](../../TABLE.md#level-384).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_192_eta_1m3_2p9_3p1_4m3_6m3_12p1_24p1_32p2_64m1_96m1_192p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^9 η(3z) η(4z)^(-3) η(6z)^(-3) η(12z) η(24z) η(32z)^2 η(64z)^(-1) η(96z)^(-1) η(192z)` at level 384. -/
abbrev cuspForm_192_eta_1m3_2p9_3p1_4m3_6m3_12p1_24p1_32p2_64m1_96m1_192p1_old_384_1 : gamma0CuspForms 384 :=
  gamma0RescaleToLevel cuspForm_192_eta_1m3_2p9_3p1_4m3_6m3_12p1_24p1_32p2_64m1_96m1_192p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_192_eta_1m3_2p9_3p1_4m3_6m3_12p1_24p1_32p2_64m1_96m1_192p1_old_384_1_eq_eta :
    cuspForm_192_eta_1m3_2p9_3p1_4m3_6m3_12p1_24p1_32p2_64m1_96m1_192p1_old_384_1 =
      etaQuotientCuspForm 384 sparse![384; 0 => -3, 1 => 9, 2 => 1, 3 => -3, 5 => -3, 11 => 1, 23 => 1, 31 => 2, 63 => -1, 95 => -1, 191 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_192_eta_1m3_2p9_3p1_4m3_6m3_12p1_24p1_32p2_64m1_96m1_192p1_old_384_1_first_coeffs :
    first_coeffs 100 cuspForm_192_eta_1m3_2p9_3p1_4m3_6m3_12p1_24p1_32p2_64m1_96m1_192p1_old_384_1 =
    [0, 0, 0, 0, 0, 1, 3, 0, -6, -3, 0, 0, 6, 0, -6, 0, 0, 6, 6, 0,
     0, -3, 0, 0, 6, 0, -12, 0, 0, -1, 0, 0, 0, -3, 0, 0, 0, -2, 0, 0,
     12, 6, 0, 0, -24, 3, 12, 0, 0, -12, 0, 0, 0, 11, 3, 0, 0, 3, 24, 0,
     -12, 2, -6, 0, 0, -6, -6, 0, 0, 0, -12, 0, -6, 0, 12, 0, 24, -12, -6, 0,
     0, 6, -24, 0, 0, -10, 0, 0, -24, 0, -12, 0, 48, 3, 12, 0, 0, 24, 0, 0] := by
  eta_coeff

end WeightTwoCusps
