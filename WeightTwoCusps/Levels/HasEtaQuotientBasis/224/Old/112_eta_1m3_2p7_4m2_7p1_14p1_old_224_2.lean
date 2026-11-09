module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«112».New.«112_eta_1m3_2p7_4m2_7p1_14p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 224

The eta expression is `η(2z)^(-3) η(4z)^7 η(8z)^(-2) η(14z) η(28z)`; see
[the local level table](../../TABLE.md#level-224).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-3) η(4z)^7 η(8z)^(-2) η(14z) η(28z)` at level 224. -/
abbrev cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1_old_224_2 : gamma0CuspForms 224 :=
  gamma0Rescale cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1_old_224_2_eq_eta :
    cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1_old_224_2 =
      etaQuotientCuspForm 224 sparse![224; 1 => -3, 3 => 7, 7 => -2, 13 => 1, 27 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1_old_224_2_first_coeffs :
    first_coeffs 100 cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1_old_224_2 =
    [0, 0, 1, 0, 3, 0, 2, 0, 1, 0, 4, 0, 2, 0, 1, 0, 3, 0, -3, 0,
     0, 0, 4, 0, -2, 0, 0, 0, -1, 0, -4, 0, -3, 0, -2, 0, -5, 0, -10, 0,
     0, 0, -2, 0, -8, 0, 4, 0, -6, 0, -9, 0, 4, 0, -4, 0, 1, 0, 2, 0,
     -8, 0, -4, 0, 3, 0, 0, 0, -14, 0, 0, 0, 1, 0, 2, 0, 14, 0, -4, 0,
     0, 0, 6, 0, 2, 0, 4, 0, 0, 0, -4, 0, 8, 0, 12, 0, 6, 0, 1, 0] := by
  eta_coeff

end WeightTwoCusps
