module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«114».New.«114_eta_2p2_3p1_6m1_19p2_57m1_114p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 228

The eta expression is `η(4z)^2 η(6z) η(12z)^(-1) η(38z)^2 η(114z)^(-1) η(228z)`; see
[the local level table](../../TABLE.md#level-228).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_114_eta_2p2_3p1_6m1_19p2_57m1_114p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^2 η(6z) η(12z)^(-1) η(38z)^2 η(114z)^(-1) η(228z)` at level 228. -/
abbrev cuspForm_114_eta_2p2_3p1_6m1_19p2_57m1_114p1_old_228_2 : gamma0CuspForms 228 :=
  gamma0Rescale cuspForm_114_eta_2p2_3p1_6m1_19p2_57m1_114p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_114_eta_2p2_3p1_6m1_19p2_57m1_114p1_old_228_2_eq_eta :
    cuspForm_114_eta_2p2_3p1_6m1_19p2_57m1_114p1_old_228_2 =
      etaQuotientCuspForm 228 sparse![228; 3 => 2, 5 => 1, 11 => -1, 37 => 2, 113 => -1, 227 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_114_eta_2p2_3p1_6m1_19p2_57m1_114p1_old_228_2_first_coeffs :
    first_coeffs 100 cuspForm_114_eta_2p2_3p1_6m1_19p2_57m1_114p1_old_228_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -2, 0, -1, 0, -1, 0, 2, 0,
     2, 0, 1, 0, 1, 0, -3, 0, 2, 0, 1, 0, -1, 0, -1, 0, -2, 0, -1, 0,
     -3, 0, 1, 0, 1, 0, -1, 0, 0, 0, 5, 0, 3, 0, 2, 0, -2, 0, -3, 0,
     -3, 0, -2, 0, 7, 0, -4, 0, -2, 0, 1, 0, 3, 0, 4, 0, 2, 0, 3, 0,
     -1, 0, -5, 0, -6, 0, 1, 0, -2, 0, 0, 0, 0, 0, -4, 0, -1, 0, 1, 0] := by
  eta_coeff

end WeightTwoCusps
