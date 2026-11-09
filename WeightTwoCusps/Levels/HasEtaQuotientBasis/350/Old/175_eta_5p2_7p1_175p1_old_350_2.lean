module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«175».New.«175_eta_5p2_7p1_175p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 350

The eta expression is `η(10z)^2 η(14z) η(350z)`; see
[the local level table](../../TABLE.md#level-350).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_175_eta_5p2_7p1_175p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(10z)^2 η(14z) η(350z)` at level 350. -/
abbrev cuspForm_175_eta_5p2_7p1_175p1_old_350_2 : gamma0CuspForms 350 :=
  gamma0Rescale cuspForm_175_eta_5p2_7p1_175p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_175_eta_5p2_7p1_175p1_old_350_2_eq_eta :
    cuspForm_175_eta_5p2_7p1_175p1_old_350_2 =
      etaQuotientCuspForm 350 sparse![350; 9 => 2, 13 => 1, 349 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_175_eta_5p2_7p1_175p1_old_350_2_first_coeffs :
    first_coeffs 100 cuspForm_175_eta_5p2_7p1_175p1_old_350_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
     0, 0, 0, 0, 0, 0, -2, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     2, 0, 0, 0, -1, 0, 2, 0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 0, 0, 0,
     -2, 0, 0, 0, 1, 0, 2, 0, 0, 0, -1, 0, 0, 0, -2, 0, -2, 0, 0, 0,
     -2, 0, 0, 0, -1, 0, 1, 0, 0, 0, 2, 0, 0, 0, -2, 0, -4, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
