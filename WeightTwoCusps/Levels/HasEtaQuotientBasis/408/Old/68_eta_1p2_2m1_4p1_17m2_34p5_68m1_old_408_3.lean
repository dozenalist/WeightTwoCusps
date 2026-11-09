module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«68».New.«68_eta_1p2_2m1_4p1_17m2_34p5_68m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 408

The eta expression is `η(3z)^2 η(6z)^(-1) η(12z) η(51z)^(-2) η(102z)^5 η(204z)^(-1)`; see
[the local level table](../../TABLE.md#level-408).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_68_eta_1p2_2m1_4p1_17m2_34p5_68m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^2 η(6z)^(-1) η(12z) η(51z)^(-2) η(102z)^5 η(204z)^(-1)` at level 408. -/
abbrev cuspForm_68_eta_1p2_2m1_4p1_17m2_34p5_68m1_old_408_3 : gamma0CuspForms 408 :=
  gamma0RescaleToLevel cuspForm_68_eta_1p2_2m1_4p1_17m2_34p5_68m1 3 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_68_eta_1p2_2m1_4p1_17m2_34p5_68m1_old_408_3_eq_eta :
    cuspForm_68_eta_1p2_2m1_4p1_17m2_34p5_68m1_old_408_3 =
      etaQuotientCuspForm 408 sparse![408; 2 => 2, 5 => -1, 11 => 1, 50 => -2, 101 => 5, 203 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_68_eta_1p2_2m1_4p1_17m2_34p5_68m1_old_408_3_first_coeffs :
    first_coeffs 100 cuspForm_68_eta_1p2_2m1_4p1_17m2_34p5_68m1_old_408_3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0,
     0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, -2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0,
     4, 0, 0, -4, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0,
     0, 0, 0, 0, -8, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -6, 0, 0, 4] := by
  eta_coeff

end WeightTwoCusps
