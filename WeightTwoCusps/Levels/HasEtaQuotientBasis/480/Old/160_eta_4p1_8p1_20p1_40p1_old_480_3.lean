module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«160».New.«160_eta_4p1_8p1_20p1_40p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(12z) η(24z) η(60z) η(120z)`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_160_eta_4p1_8p1_20p1_40p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(12z) η(24z) η(60z) η(120z)` at level 480. -/
abbrev cuspForm_160_eta_4p1_8p1_20p1_40p1_old_480_3 : gamma0CuspForms 480 :=
  gamma0Rescale cuspForm_160_eta_4p1_8p1_20p1_40p1 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_160_eta_4p1_8p1_20p1_40p1_old_480_3_eq_eta :
    cuspForm_160_eta_4p1_8p1_20p1_40p1_old_480_3 =
      etaQuotientCuspForm 480 sparse![480; 11 => 1, 23 => 1, 59 => 1, 119 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_160_eta_4p1_8p1_20p1_40p1_old_480_3_first_coeffs :
    first_coeffs 100 cuspForm_160_eta_4p1_8p1_20p1_40p1_old_480_3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
