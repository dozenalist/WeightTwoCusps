module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«75».New.«75_eta_1p1_5p1_15p1_75p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 150

The eta expression is `η(2z) η(10z) η(30z) η(150z)`; see
[the local level table](../../TABLE.md#level-150).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_75_eta_1p1_5p1_15p1_75p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(10z) η(30z) η(150z)` at level 150. -/
abbrev cuspForm_75_eta_1p1_5p1_15p1_75p1_old_150_2 : gamma0CuspForms 150 :=
  gamma0Rescale cuspForm_75_eta_1p1_5p1_15p1_75p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_75_eta_1p1_5p1_15p1_75p1_old_150_2_eq_eta :
    cuspForm_75_eta_1p1_5p1_15p1_75p1_old_150_2 =
      etaQuotientCuspForm 150 sparse![150; 1 => 1, 9 => 1, 29 => 1, 149 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_75_eta_1p1_5p1_15p1_75p1_old_150_2_first_coeffs :
    first_coeffs 100 cuspForm_75_eta_1p1_5p1_15p1_75p1_old_150_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 2, 0, 0, 0, 0, 0, -2, 0, 1, 0, -1, 0, 0, 0, 0, 0, -3, 0,
     1, 0, 1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 4, 0,
     -1, 0, -1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0,
     -3, 0, -6, 0, 0, 0, 0, 0, 0, 0, -1, 0, 4, 0, 0, 0, 0, 0, 3, 0] := by
  eta_coeff

end WeightTwoCusps
