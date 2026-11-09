module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«160».New.«160_eta_4p1_8p1_20p1_40p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 320

The eta expression is `η(8z) η(16z) η(40z) η(80z)`; see
[the local level table](../../TABLE.md#level-320).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_160_eta_4p1_8p1_20p1_40p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(8z) η(16z) η(40z) η(80z)` at level 320. -/
abbrev cuspForm_160_eta_4p1_8p1_20p1_40p1_old_320_2 : gamma0CuspForms 320 :=
  gamma0Rescale cuspForm_160_eta_4p1_8p1_20p1_40p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_160_eta_4p1_8p1_20p1_40p1_old_320_2_eq_eta :
    cuspForm_160_eta_4p1_8p1_20p1_40p1_old_320_2 =
      etaQuotientCuspForm 320 sparse![320; 7 => 1, 15 => 1, 39 => 1, 79 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_160_eta_4p1_8p1_20p1_40p1_old_320_2_first_coeffs :
    first_coeffs 100 cuspForm_160_eta_4p1_8p1_20p1_40p1_old_320_2 =
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0,
     0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0,
     0, 0, 2, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, -2, 0,
     0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
