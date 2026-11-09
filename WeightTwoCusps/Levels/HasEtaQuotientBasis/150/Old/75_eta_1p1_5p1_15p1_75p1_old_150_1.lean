module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«75».New.«75_eta_1p1_5p1_15p1_75p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 150

The eta expression is `η(z) η(5z) η(15z) η(75z)`; see
[the local level table](../../TABLE.md#level-150).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_75_eta_1p1_5p1_15p1_75p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(5z) η(15z) η(75z)` at level 150. -/
abbrev cuspForm_75_eta_1p1_5p1_15p1_75p1_old_150_1 : gamma0CuspForms 150 :=
  gamma0RescaleToLevel cuspForm_75_eta_1p1_5p1_15p1_75p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_75_eta_1p1_5p1_15p1_75p1_old_150_1_eq_eta :
    cuspForm_75_eta_1p1_5p1_15p1_75p1_old_150_1 =
      etaQuotientCuspForm 150 sparse![150; 0 => 1, 4 => 1, 14 => 1, 74 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_75_eta_1p1_5p1_15p1_75p1_old_150_1_first_coeffs :
    first_coeffs 100 cuspForm_75_eta_1p1_5p1_15p1_75p1_old_150_1 =
    [0, 0, 0, 0, 1, -1, -1, 0, 0, 0, 1, 2, 0, 0, -2, 1, -1, 0, 0, -3,
     1, 1, 0, 0, 1, -1, 0, 0, 0, 4, -1, -1, 0, 0, 2, 0, 1, 0, 0, -1,
     -3, -6, 0, 0, 0, -1, 4, 0, 0, 3, 1, 0, 0, 0, -1, 4, 0, 0, 0, -2,
     -1, 3, 0, 0, -5, 2, 0, 0, 0, -2, 0, 0, 0, 0, -2, 1, -2, 0, 0, 0,
     1, 0, 0, 0, 2, -2, 2, 0, 0, 2, 1, -1, 0, 0, 4, -4, 1, 0, 0, 2] := by
  eta_coeff

end WeightTwoCusps
