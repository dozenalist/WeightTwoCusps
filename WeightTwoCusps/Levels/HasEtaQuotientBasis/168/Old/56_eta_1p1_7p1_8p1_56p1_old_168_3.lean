module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«56».New.«56_eta_1p1_7p1_8p1_56p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 168

The eta expression is `η(3z) η(21z) η(24z) η(168z)`; see
[the local level table](../../TABLE.md#level-168).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_56_eta_1p1_7p1_8p1_56p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z) η(21z) η(24z) η(168z)` at level 168. -/
abbrev cuspForm_56_eta_1p1_7p1_8p1_56p1_old_168_3 : gamma0CuspForms 168 :=
  gamma0Rescale cuspForm_56_eta_1p1_7p1_8p1_56p1 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_56_eta_1p1_7p1_8p1_56p1_old_168_3_eq_eta :
    cuspForm_56_eta_1p1_7p1_8p1_56p1_old_168_3 =
      etaQuotientCuspForm 168 sparse![168; 2 => 1, 20 => 1, 23 => 1, 167 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_56_eta_1p1_7p1_8p1_56p1_old_168_3_first_coeffs :
    first_coeffs 100 cuspForm_56_eta_1p1_7p1_8p1_56p1_old_168_3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1,
     0, 0, 0, 0, 0, -2, 0, 0, -1, 0, 0, -2, 0, 0, 0, 0, 0, -1, 0, 0,
     0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, -2, 0, 0, 4, 0, 0, 0, 0,
     0, -2, 0, 0, -1, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
