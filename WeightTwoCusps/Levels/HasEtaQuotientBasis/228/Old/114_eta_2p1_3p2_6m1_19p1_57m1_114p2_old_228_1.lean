module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«114».New.«114_eta_2p1_3p2_6m1_19p1_57m1_114p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 228

The eta expression is `η(2z) η(3z)^2 η(6z)^(-1) η(19z) η(57z)^(-1) η(114z)^2`; see
[the local level table](../../TABLE.md#level-228).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_114_eta_2p1_3p2_6m1_19p1_57m1_114p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(3z)^2 η(6z)^(-1) η(19z) η(57z)^(-1) η(114z)^2` at level 228. -/
abbrev cuspForm_114_eta_2p1_3p2_6m1_19p1_57m1_114p2_old_228_1 : gamma0CuspForms 228 :=
  gamma0RescaleToLevel cuspForm_114_eta_2p1_3p2_6m1_19p1_57m1_114p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_114_eta_2p1_3p2_6m1_19p1_57m1_114p2_old_228_1_eq_eta :
    cuspForm_114_eta_2p1_3p2_6m1_19p1_57m1_114p2_old_228_1 =
      etaQuotientCuspForm 228 sparse![228; 1 => 1, 2 => 2, 5 => -1, 18 => 1, 56 => -1, 113 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_114_eta_2p1_3p2_6m1_19p1_57m1_114p2_old_228_1_first_coeffs :
    first_coeffs 100 cuspForm_114_eta_2p1_3p2_6m1_19p1_57m1_114p2_old_228_1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, -2, -1, 2, 0, 2, 0, 0, 1, 0,
     2, -2, -1, 0, -2, -2, 0, -1, 0, 1, 4, 1, -3, 0, 0, 0, 0, 1, -1, 0,
     2, 3, 0, 2, 0, -2, -1, 0, 1, -2, -1, -1, 1, -4, 0, -2, -1, 1, -6, 4,
     -2, 0, 2, 2, 4, 3, 2, -1, -2, 1, 5, -1, 2, 0, 2, -3, 1, 2, -5, -4,
     -2, 0, 2, -2, -3, 0, -1, 6, 2, -5, -3, 0, 0, 0, -1, -1, 2, -1, 6, 2] := by
  eta_coeff

end WeightTwoCusps
