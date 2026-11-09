module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«114».New.«114_eta_2p1_3p1_19m2_38p3_57p3_114m2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 228

The eta expression is `η(2z) η(3z) η(19z)^(-2) η(38z)^3 η(57z)^3 η(114z)^(-2)`; see
[the local level table](../../TABLE.md#level-228).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_114_eta_2p1_3p1_19m2_38p3_57p3_114m2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(3z) η(19z)^(-2) η(38z)^3 η(57z)^3 η(114z)^(-2)` at level 228. -/
abbrev cuspForm_114_eta_2p1_3p1_19m2_38p3_57p3_114m2_old_228_1 : gamma0CuspForms 228 :=
  gamma0RescaleToLevel cuspForm_114_eta_2p1_3p1_19m2_38p3_57p3_114m2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_114_eta_2p1_3p1_19m2_38p3_57p3_114m2_old_228_1_eq_eta :
    cuspForm_114_eta_2p1_3p1_19m2_38p3_57p3_114m2_old_228_1 =
      etaQuotientCuspForm 228 sparse![228; 1 => 1, 2 => 1, 18 => -2, 37 => 3, 56 => 3, 113 => -2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_114_eta_2p1_3p1_19m2_38p3_57p3_114m2_old_228_1_first_coeffs :
    first_coeffs 100 cuspForm_114_eta_2p1_3p1_19m2_38p3_57p3_114m2_old_228_1 =
    [0, 1, 0, -1, -1, -1, 1, -1, 1, 1, 0, 2, 0, 0, -1, 1, 1, -1, -2, 0,
     1, -1, -1, -2, -3, 1, -2, 2, 3, 0, 5, 0, 1, -2, 3, 2, -1, -4, 0, 1,
     -3, 1, -2, -4, 0, -1, -1, 3, 0, 6, 1, 0, -3, 5, 2, 0, -6, 0, 1, -5,
     3, 0, -3, -1, 1, -5, 2, 2, 5, 1, -1, -5, 5, 1, 3, -6, 1, 2, -5, 5,
     3, -2, -2, 2, -6, 0, 3, 2, 0, -1, -6, 1, -2, 7, -2, 2, 5, -3, 1, 2] := by
  eta_coeff

end WeightTwoCusps
