module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«112».New.«112_eta_1m3_2p7_4m2_7p1_14p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 448

The eta expression is `η(4z)^(-3) η(8z)^7 η(16z)^(-2) η(28z) η(56z)`; see
[the local level table](../../TABLE.md#level-448).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^(-3) η(8z)^7 η(16z)^(-2) η(28z) η(56z)` at level 448. -/
abbrev cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1_old_448_4 : gamma0CuspForms 448 :=
  gamma0Rescale cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1_old_448_4_eq_eta :
    cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1_old_448_4 =
      etaQuotientCuspForm 448 sparse![448; 3 => -3, 7 => 7, 15 => -2, 27 => 1, 55 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1_old_448_4_first_coeffs :
    first_coeffs 100 cuspForm_112_eta_1m3_2p7_4m2_7p1_14p1_old_448_4 =
    [0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0,
     4, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, -3, 0, 0, 0,
     0, 0, 0, 0, 4, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     -4, 0, 0, 0, -3, 0, 0, 0, -2, 0, 0, 0, -5, 0, 0, 0, -10, 0, 0, 0,
     0, 0, 0, 0, -2, 0, 0, 0, -8, 0, 0, 0, 4, 0, 0, 0, -6, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
