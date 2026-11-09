module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«224».New.«224_eta_1m3_2p7_4m2_7p1_14m3_28p6_56m2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 448

The eta expression is `η(z)^(-3) η(2z)^7 η(4z)^(-2) η(7z) η(14z)^(-3) η(28z)^6 η(56z)^(-2)`; see
[the local level table](../../TABLE.md#level-448).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_224_eta_1m3_2p7_4m2_7p1_14m3_28p6_56m2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(4z)^(-2) η(7z) η(14z)^(-3) η(28z)^6 η(56z)^(-2)` at level 448. -/
abbrev cuspForm_224_eta_1m3_2p7_4m2_7p1_14m3_28p6_56m2_old_448_1 : gamma0CuspForms 448 :=
  gamma0RescaleToLevel cuspForm_224_eta_1m3_2p7_4m2_7p1_14m3_28p6_56m2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_224_eta_1m3_2p7_4m2_7p1_14m3_28p6_56m2_old_448_1_eq_eta :
    cuspForm_224_eta_1m3_2p7_4m2_7p1_14m3_28p6_56m2_old_448_1 =
      etaQuotientCuspForm 448 sparse![448; 0 => -3, 1 => 7, 3 => -2, 6 => 1, 13 => -3, 27 => 6, 55 => -2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_224_eta_1m3_2p7_4m2_7p1_14m3_28p6_56m2_old_448_1_first_coeffs :
    first_coeffs 100 cuspForm_224_eta_1m3_2p7_4m2_7p1_14m3_28p6_56m2_old_448_1 =
    [0, 1, 3, 2, 1, 4, 2, 1, 3, -3, 0, 4, -2, 0, -1, 0, 9, 6, -1, 6,
     8, 2, 4, -8, -6, 7, -4, -4, -3, -6, 4, 4, -9, -8, 2, 0, -7, -6, -10, -8,
     0, -10, -2, -4, -8, -4, -4, -4, -18, 1, -3, -4, 4, -10, -4, 0, 3, 0, -2, -10,
     8, 12, -4, 1, 9, 4, 0, 8, -10, 8, 4, 0, 3, -6, -2, -10, 18, -8, -12, 16,
     0, -7, 10, -2, -2, 16, -12, 4, 0, -6, -8, -4, -8, 0, 28, 0, 18, 14, 3, 4] := by
  eta_coeff

end WeightTwoCusps
