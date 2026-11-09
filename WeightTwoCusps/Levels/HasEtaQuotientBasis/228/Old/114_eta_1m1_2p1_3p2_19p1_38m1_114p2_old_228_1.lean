module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«114».New.«114_eta_1m1_2p1_3p2_19p1_38m1_114p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 228

The eta expression is `η(z)^(-1) η(2z) η(3z)^2 η(19z) η(38z)^(-1) η(114z)^2`; see
[the local level table](../../TABLE.md#level-228).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_114_eta_1m1_2p1_3p2_19p1_38m1_114p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z)^2 η(19z) η(38z)^(-1) η(114z)^2` at level 228. -/
abbrev cuspForm_114_eta_1m1_2p1_3p2_19p1_38m1_114p2_old_228_1 : gamma0CuspForms 228 :=
  gamma0RescaleToLevel cuspForm_114_eta_1m1_2p1_3p2_19p1_38m1_114p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_114_eta_1m1_2p1_3p2_19p1_38m1_114p2_old_228_1_eq_eta :
    cuspForm_114_eta_1m1_2p1_3p2_19p1_38m1_114p2_old_228_1 =
      etaQuotientCuspForm 228 sparse![228; 0 => -1, 1 => 1, 2 => 2, 18 => 1, 37 => -1, 113 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_114_eta_1m1_2p1_3p2_19p1_38m1_114p2_old_228_1_first_coeffs :
    first_coeffs 100 cuspForm_114_eta_1m1_2p1_3p2_19p1_38m1_114p2_old_228_1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, -1, 0, -1, 0, 0,
     -1, 0, -2, -1, 1, 0, -1, -1, -2, -1, -2, 1, 0, -2, 1, 1, 0, -1, 0, 2,
     1, 2, 1, -2, 2, 1, 2, 0, 0, 2, -2, 2, 2, 1, 0, 0, 1, 0, 0, -1,
     1, 0, 1, -1, 0, 0, 1, -1, -2, 1, -2, -2, -2, 0, 3, 0, 0, 1, -1, 3,
     1, -2, -2, 0, 0, 0, 2, 2, -2, 0, 3, 1, -3, -2, 1, 0, -3, 0, -5, -2] := by
  eta_coeff

end WeightTwoCusps
