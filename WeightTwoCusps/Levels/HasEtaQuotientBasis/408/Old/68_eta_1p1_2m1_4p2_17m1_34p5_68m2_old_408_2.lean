module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«68».New.«68_eta_1p1_2m1_4p2_17m1_34p5_68m2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 408

The eta expression is `η(2z) η(4z)^(-1) η(8z)^2 η(34z)^(-1) η(68z)^5 η(136z)^(-2)`; see
[the local level table](../../TABLE.md#level-408).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_68_eta_1p1_2m1_4p2_17m1_34p5_68m2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(4z)^(-1) η(8z)^2 η(34z)^(-1) η(68z)^5 η(136z)^(-2)` at level 408. -/
abbrev cuspForm_68_eta_1p1_2m1_4p2_17m1_34p5_68m2_old_408_2 : gamma0CuspForms 408 :=
  gamma0RescaleToLevel cuspForm_68_eta_1p1_2m1_4p2_17m1_34p5_68m2 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_68_eta_1p1_2m1_4p2_17m1_34p5_68m2_old_408_2_eq_eta :
    cuspForm_68_eta_1p1_2m1_4p2_17m1_34p5_68m2_old_408_2 =
      etaQuotientCuspForm 408 sparse![408; 1 => 1, 3 => -1, 7 => 2, 33 => -1, 67 => 5, 135 => -2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_68_eta_1p1_2m1_4p2_17m1_34p5_68m2_old_408_2_first_coeffs :
    first_coeffs 100 cuspForm_68_eta_1p1_2m1_4p2_17m1_34p5_68m2_old_408_2 =
    [0, 0, 1, 0, -1, 0, 0, 0, -1, 0, -1, 0, 1, 0, 1, 0, 1, 0, -1, 0,
     1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -2, 0, -1, 0, 0, 0, 1, 0, -2, 0,
     1, 0, 0, 0, -3, 0, 1, 0, 1, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3, 0,
     0, 0, 1, 0, -3, 0, -2, 0, 0, 0, -2, 0, 1, 0, 1, 0, 4, 0, 2, 0,
     -3, 0, -4, 0, -4, 0, 4, 0, -3, 0, -1, 0, -2, 0, 0, 0, 1, 0, 5, 0] := by
  eta_coeff

end WeightTwoCusps
