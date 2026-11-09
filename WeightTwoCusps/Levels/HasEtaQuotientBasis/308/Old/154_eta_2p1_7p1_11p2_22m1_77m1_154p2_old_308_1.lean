module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«154».New.«154_eta_2p1_7p1_11p2_22m1_77m1_154p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 308

The eta expression is `η(2z) η(7z) η(11z)^2 η(22z)^(-1) η(77z)^(-1) η(154z)^2`; see
[the local level table](../../TABLE.md#level-308).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_154_eta_2p1_7p1_11p2_22m1_77m1_154p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(7z) η(11z)^2 η(22z)^(-1) η(77z)^(-1) η(154z)^2` at level 308. -/
abbrev cuspForm_154_eta_2p1_7p1_11p2_22m1_77m1_154p2_old_308_1 : gamma0CuspForms 308 :=
  gamma0RescaleToLevel cuspForm_154_eta_2p1_7p1_11p2_22m1_77m1_154p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_154_eta_2p1_7p1_11p2_22m1_77m1_154p2_old_308_1_eq_eta :
    cuspForm_154_eta_2p1_7p1_11p2_22m1_77m1_154p2_old_308_1 =
      etaQuotientCuspForm 308 sparse![308; 1 => 1, 6 => 1, 10 => 2, 21 => -1, 76 => -1, 153 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_154_eta_2p1_7p1_11p2_22m1_77m1_154p2_old_308_1_first_coeffs :
    first_coeffs 100 cuspForm_154_eta_2p1_7p1_11p2_22m1_77m1_154p2_old_308_1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, -1, 0, 0, -1, 0, 1,
     1, -1, 0, 2, 0, 2, 1, -1, 3, 0, -2, -3, -2, 0, -2, 0, 0, -2, 1, -2,
     -1, 1, 2, 0, 0, 5, 0, 0, 1, 1, 0, 2, -2, 0, 4, 1, -4, 0, -2, 0,
     2, -4, 1, 1, 2, -2, -2, 0, -1, -1, -2, -2, 6, -1, 2, -3, -1, 0, -4, 2,
     1, 0, -2, -1, -4, 2, 2, 4, 0, 1, -1, 1, 2, -2, 1, 0, 2, 3, 2, 2] := by
  eta_coeff

end WeightTwoCusps
