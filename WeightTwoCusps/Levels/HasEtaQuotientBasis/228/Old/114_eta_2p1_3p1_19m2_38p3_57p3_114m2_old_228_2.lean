module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«114».New.«114_eta_2p1_3p1_19m2_38p3_57p3_114m2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 228

The eta expression is `η(4z) η(6z) η(38z)^(-2) η(76z)^3 η(114z)^3 η(228z)^(-2)`; see
[the local level table](../../TABLE.md#level-228).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_114_eta_2p1_3p1_19m2_38p3_57p3_114m2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z) η(6z) η(38z)^(-2) η(76z)^3 η(114z)^3 η(228z)^(-2)` at level 228. -/
abbrev cuspForm_114_eta_2p1_3p1_19m2_38p3_57p3_114m2_old_228_2 : gamma0CuspForms 228 :=
  gamma0Rescale cuspForm_114_eta_2p1_3p1_19m2_38p3_57p3_114m2 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_114_eta_2p1_3p1_19m2_38p3_57p3_114m2_old_228_2_eq_eta :
    cuspForm_114_eta_2p1_3p1_19m2_38p3_57p3_114m2_old_228_2 =
      etaQuotientCuspForm 228 sparse![228; 3 => 1, 5 => 1, 37 => -2, 75 => 3, 113 => 3, 227 => -2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_114_eta_2p1_3p1_19m2_38p3_57p3_114m2_old_228_2_first_coeffs :
    first_coeffs 100 cuspForm_114_eta_2p1_3p1_19m2_38p3_57p3_114m2_old_228_2 =
    [0, 0, 1, 0, 0, 0, -1, 0, -1, 0, -1, 0, 1, 0, -1, 0, 1, 0, 1, 0,
     0, 0, 2, 0, 0, 0, 0, 0, -1, 0, 1, 0, 1, 0, -1, 0, -2, 0, 0, 0,
     1, 0, -1, 0, -1, 0, -2, 0, -3, 0, 1, 0, -2, 0, 2, 0, 3, 0, 0, 0,
     5, 0, 0, 0, 1, 0, -2, 0, 3, 0, 2, 0, -1, 0, -4, 0, 0, 0, 1, 0,
     -3, 0, 1, 0, -2, 0, -4, 0, 0, 0, -1, 0, -1, 0, 3, 0, 0, 0, 6, 0] := by
  eta_coeff

end WeightTwoCusps
