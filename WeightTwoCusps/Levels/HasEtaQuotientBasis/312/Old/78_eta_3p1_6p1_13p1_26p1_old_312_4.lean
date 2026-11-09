module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«78».New.«78_eta_3p1_6p1_13p1_26p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 312

The eta expression is `η(12z) η(24z) η(52z) η(104z)`; see
[the local level table](../../TABLE.md#level-312).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_78_eta_3p1_6p1_13p1_26p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(12z) η(24z) η(52z) η(104z)` at level 312. -/
abbrev cuspForm_78_eta_3p1_6p1_13p1_26p1_old_312_4 : gamma0CuspForms 312 :=
  gamma0Rescale cuspForm_78_eta_3p1_6p1_13p1_26p1 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_78_eta_3p1_6p1_13p1_26p1_old_312_4_eq_eta :
    cuspForm_78_eta_3p1_6p1_13p1_26p1_old_312_4 =
      etaQuotientCuspForm 312 sparse![312; 11 => 1, 23 => 1, 51 => 1, 103 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_78_eta_3p1_6p1_13p1_26p1_old_312_4_first_coeffs :
    first_coeffs 100 cuspForm_78_eta_3p1_6p1_13p1_26p1_old_312_4 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     -1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
