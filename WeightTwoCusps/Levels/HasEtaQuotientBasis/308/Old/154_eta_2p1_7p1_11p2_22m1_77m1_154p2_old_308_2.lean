module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«154».New.«154_eta_2p1_7p1_11p2_22m1_77m1_154p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 308

The eta expression is `η(4z) η(14z) η(22z)^2 η(44z)^(-1) η(154z)^(-1) η(308z)^2`; see
[the local level table](../../TABLE.md#level-308).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_154_eta_2p1_7p1_11p2_22m1_77m1_154p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z) η(14z) η(22z)^2 η(44z)^(-1) η(154z)^(-1) η(308z)^2` at level 308. -/
abbrev cuspForm_154_eta_2p1_7p1_11p2_22m1_77m1_154p2_old_308_2 : gamma0CuspForms 308 :=
  gamma0Rescale cuspForm_154_eta_2p1_7p1_11p2_22m1_77m1_154p2 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_154_eta_2p1_7p1_11p2_22m1_77m1_154p2_old_308_2_eq_eta :
    cuspForm_154_eta_2p1_7p1_11p2_22m1_77m1_154p2_old_308_2 =
      etaQuotientCuspForm 308 sparse![308; 3 => 1, 13 => 1, 21 => 2, 43 => -1, 153 => -1, 307 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_154_eta_2p1_7p1_11p2_22m1_77m1_154p2_old_308_2_first_coeffs :
    first_coeffs 100 cuspForm_154_eta_2p1_7p1_11p2_22m1_77m1_154p2_old_308_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0,
     1, 0, -1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 1, 0, -1, 0, 3, 0, 0, 0,
     -2, 0, -3, 0, -2, 0, 0, 0, -2, 0, 0, 0, 0, 0, -2, 0, 1, 0, -2, 0,
     -1, 0, 1, 0, 2, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 1, 0, 1, 0] := by
  eta_coeff

end WeightTwoCusps
