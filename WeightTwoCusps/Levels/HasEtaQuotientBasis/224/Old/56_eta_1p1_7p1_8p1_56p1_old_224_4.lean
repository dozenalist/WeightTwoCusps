module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«56».New.«56_eta_1p1_7p1_8p1_56p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 224

The eta expression is `η(4z) η(28z) η(32z) η(224z)`; see
[the local level table](../../TABLE.md#level-224).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_56_eta_1p1_7p1_8p1_56p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z) η(28z) η(32z) η(224z)` at level 224. -/
abbrev cuspForm_56_eta_1p1_7p1_8p1_56p1_old_224_4 : gamma0CuspForms 224 :=
  gamma0Rescale cuspForm_56_eta_1p1_7p1_8p1_56p1 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_56_eta_1p1_7p1_8p1_56p1_old_224_4_eq_eta :
    cuspForm_56_eta_1p1_7p1_8p1_56p1_old_224_4 =
      etaQuotientCuspForm 224 sparse![224; 3 => 1, 27 => 1, 31 => 1, 223 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_56_eta_1p1_7p1_8p1_56p1_old_224_4_first_coeffs :
    first_coeffs 100 cuspForm_56_eta_1p1_7p1_8p1_56p1_old_224_4 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0,
     -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
     -2, 0, 0, 0, -1, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, -2, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
