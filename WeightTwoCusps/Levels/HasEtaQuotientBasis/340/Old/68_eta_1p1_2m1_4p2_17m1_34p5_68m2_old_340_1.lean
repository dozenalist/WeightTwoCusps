module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«68».New.«68_eta_1p1_2m1_4p2_17m1_34p5_68m2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 340

The eta expression is `η(z) η(2z)^(-1) η(4z)^2 η(17z)^(-1) η(34z)^5 η(68z)^(-2)`; see
[the local level table](../../TABLE.md#level-340).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_68_eta_1p1_2m1_4p2_17m1_34p5_68m2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(2z)^(-1) η(4z)^2 η(17z)^(-1) η(34z)^5 η(68z)^(-2)` at level 340. -/
abbrev cuspForm_68_eta_1p1_2m1_4p2_17m1_34p5_68m2_old_340_1 : gamma0CuspForms 340 :=
  gamma0RescaleToLevel cuspForm_68_eta_1p1_2m1_4p2_17m1_34p5_68m2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_68_eta_1p1_2m1_4p2_17m1_34p5_68m2_old_340_1_eq_eta :
    cuspForm_68_eta_1p1_2m1_4p2_17m1_34p5_68m2_old_340_1 =
      etaQuotientCuspForm 340 sparse![340; 0 => 1, 1 => -1, 3 => 2, 16 => -1, 33 => 5, 67 => -2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_68_eta_1p1_2m1_4p2_17m1_34p5_68m2_old_340_1_first_coeffs :
    first_coeffs 100 cuspForm_68_eta_1p1_2m1_4p2_17m1_34p5_68m2_old_340_1 =
    [0, 1, -1, 0, -1, -1, 1, 1, 1, -1, 1, 0, 1, 0, 0, -2, -1, 0, 1, -2,
     1, 0, -3, 1, 1, 1, 0, 2, 0, 3, 0, 1, -3, -2, 0, -2, 1, 1, 4, 2,
     -3, -4, -4, 4, -3, -1, -2, 0, 1, 5, 3, 0, 0, 4, -2, -2, 8, 0, -3, -4,
     0, -7, 0, -9, 3, -2, 6, 6, 0, 0, 4, -3, -5, -2, 3, 4, 4, -4, 2, 5,
     1, 3, 0, -4, -4, -1, -6, 2, -3, 6, -3, -8, -2, 4, 0, 8, 1, 4, -9, 2] := by
  eta_coeff

end WeightTwoCusps
