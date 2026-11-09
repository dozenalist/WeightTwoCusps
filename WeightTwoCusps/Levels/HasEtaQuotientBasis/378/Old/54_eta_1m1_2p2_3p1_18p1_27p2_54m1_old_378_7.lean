module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«54».New.«54_eta_1m1_2p2_3p1_18p1_27p2_54m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 378

The eta expression is `η(7z)^(-1) η(14z)^2 η(21z) η(126z) η(189z)^2 η(378z)^(-1)`; see
[the local level table](../../TABLE.md#level-378).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(7z)` of `cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(7z)^(-1) η(14z)^2 η(21z) η(126z) η(189z)^2 η(378z)^(-1)` at level 378. -/
abbrev cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_378_7 : gamma0CuspForms 378 :=
  gamma0Rescale cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1 7

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_378_7_eq_eta :
    cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_378_7 =
      etaQuotientCuspForm 378 sparse![378; 6 => -1, 13 => 2, 20 => 1, 125 => 1, 188 => 2, 377 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_378_7_first_coeffs :
    first_coeffs 100 cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_old_378_7 =
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 1, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, 0] := by
  eta_coeff

end WeightTwoCusps
