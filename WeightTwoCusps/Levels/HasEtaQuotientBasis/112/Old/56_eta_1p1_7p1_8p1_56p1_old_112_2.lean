module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«56».New.«56_eta_1p1_7p1_8p1_56p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 112

The eta expression is `η(2z) η(14z) η(16z) η(112z)`; see
[the local level table](../../TABLE.md#level-112).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_56_eta_1p1_7p1_8p1_56p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(14z) η(16z) η(112z)` at level 112. -/
abbrev cuspForm_56_eta_1p1_7p1_8p1_56p1_old_112_2 : gamma0CuspForms 112 :=
  gamma0Rescale cuspForm_56_eta_1p1_7p1_8p1_56p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_56_eta_1p1_7p1_8p1_56p1_old_112_2_eq_eta :
    cuspForm_56_eta_1p1_7p1_8p1_56p1_old_112_2 =
      etaQuotientCuspForm 112 sparse![112; 1 => 1, 13 => 1, 15 => 1, 111 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_56_eta_1p1_7p1_8p1_56p1_old_112_2_first_coeffs :
    first_coeffs 100 cuspForm_56_eta_1p1_7p1_8p1_56p1_old_112_2 =
    [0, 0, 0, 0, 0, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0,
     0, 0, 0, 0, 2, 0, 1, 0, 0, 0, -2, 0, -1, 0, -2, 0, 0, 0, -1, 0,
     0, 0, 1, 0, 0, 0, 2, 0, -2, 0, 4, 0, 0, 0, -2, 0, -1, 0, 2, 0,
     0, 0, 2, 0, 1, 0, 0, 0, 0, 0, -1, 0, -1, 0, -2, 0, 0, 0, -2, 0,
     0, 0, -2, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 2, 0, 2, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
