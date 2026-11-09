module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«112».New.«112_eta_1m3_2p7_4m2_7p1_14p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 224

The eta expression is `η(z)^(-3) η(2z)^7 η(4z)^(-2) η(7z) η(14z)`; see
[the local level table](../../TABLE.md#level-224).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(4z)^(-2) η(7z) η(14z)` at level 224. -/
abbrev cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1_old_224_1 : gamma0CuspForms 224 :=
  gamma0RescaleToLevel cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1_old_224_1_eq_eta :
    cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1_old_224_1 =
      etaQuotientCuspForm 224 sparse![224; 0 => -3, 1 => 7, 3 => -2, 6 => 1, 13 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1_old_224_1_first_coeffs :
    first_coeffs 100 cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1_old_224_1 =
    [0, 1, 3, 2, 1, 4, 2, 1, 3, -3, 0, 4, -2, 0, -1, -4, -3, -2, -5, -10,
     0, -2, -8, 4, -6, -9, 4, -4, 1, 2, -8, -4, 3, 0, -14, 0, 1, 2, 14, -4,
     0, 6, 2, 4, 0, -4, 8, 12, 6, 1, 9, 4, -4, 14, -4, 8, 3, 0, 14, 6,
     0, -4, 20, -3, -3, 4, 0, 0, 6, -8, -8, 8, 3, 18, -10, 6, 2, 4, 0, -24,
     0, 9, 2, -2, -2, -16, 0, -4, 0, -14, -16, 4, 0, 0, -20, -12, -6, -10, 3, -12] := by
  eta_coeff

end WeightTwoCusps
