module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«56».New.«56_eta_1p1_7p1_8p1_56p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 448

The eta expression is `η(2z) η(14z) η(16z) η(112z)`; see
[the local level table](../../TABLE.md#level-448).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_56_eta_1p1_7p1_8p1_56p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(14z) η(16z) η(112z)` at level 448. -/
abbrev cuspForm_56_eta_1p1_7p1_8p1_56p1_old_448_2 : gamma0CuspForms 448 :=
  gamma0RescaleToLevel cuspForm_56_eta_1p1_7p1_8p1_56p1 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_56_eta_1p1_7p1_8p1_56p1_old_448_2_eq_eta :
    cuspForm_56_eta_1p1_7p1_8p1_56p1_old_448_2 =
      etaQuotientCuspForm 448 sparse![448; 1 => 1, 13 => 1, 15 => 1, 111 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_56_eta_1p1_7p1_8p1_56p1_old_448_2_first_coeffs :
    first_coeffs 100 cuspForm_56_eta_1p1_7p1_8p1_56p1_old_448_2 =
    [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0,
     0, 0, 0, 0, 2, 0, 1, 0, 0, 0, -2, 0, -1, 0, -2, 0, 0, 0, -1, 0,
     0, 0, 1, 0, 0, 0, 2, 0, -2, 0, 4, 0, 0, 0, -2, 0, -1, 0, 2, 0,
     0, 0, 2, 0, 1, 0, 0, 0, 0, 0, -1, 0, -1, 0, -2, 0, 0, 0, -2, 0,
     0, 0, -2, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 2, 0, 2, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
