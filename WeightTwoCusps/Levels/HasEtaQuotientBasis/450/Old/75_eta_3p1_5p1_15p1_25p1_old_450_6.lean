module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«75».New.«75_eta_3p1_5p1_15p1_25p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 450

The eta expression is `η(18z) η(30z) η(90z) η(150z)`; see
[the local level table](../../TABLE.md#level-450).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(6z)` of `cuspForm_75_eta_3p1_5p1_15p1_25p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(18z) η(30z) η(90z) η(150z)` at level 450. -/
abbrev cuspForm_75_eta_3p1_5p1_15p1_25p1_old_450_6 : gamma0CuspForms 450 :=
  gamma0Rescale cuspForm_75_eta_3p1_5p1_15p1_25p1 6

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_75_eta_3p1_5p1_15p1_25p1_old_450_6_eq_eta :
    cuspForm_75_eta_3p1_5p1_15p1_25p1_old_450_6 =
      etaQuotientCuspForm 450 sparse![450; 17 => 1, 29 => 1, 89 => 1, 149 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_75_eta_3p1_5p1_15p1_25p1_old_450_6_first_coeffs :
    first_coeffs 100 cuspForm_75_eta_3p1_5p1_15p1_25p1_old_450_6 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
