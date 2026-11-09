module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«68».New.«68_eta_1m1_2p5_4m2_17p1_34m1_68p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 408

The eta expression is `η(z)^(-1) η(2z)^5 η(4z)^(-2) η(17z) η(34z)^(-1) η(68z)^2`; see
[the local level table](../../TABLE.md#level-408).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_68_eta_1m1_2p5_4m2_17p1_34m1_68p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^5 η(4z)^(-2) η(17z) η(34z)^(-1) η(68z)^2` at level 408. -/
abbrev cuspForm_68_eta_1m1_2p5_4m2_17p1_34m1_68p2_old_408_1 : gamma0CuspForms 408 :=
  gamma0RescaleToLevel cuspForm_68_eta_1m1_2p5_4m2_17p1_34m1_68p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_68_eta_1m1_2p5_4m2_17p1_34m1_68p2_old_408_1_eq_eta :
    cuspForm_68_eta_1m1_2p5_4m2_17p1_34m1_68p2_old_408_1 =
      etaQuotientCuspForm 408 sparse![408; 0 => -1, 1 => 5, 3 => -2, 16 => 1, 33 => -1, 67 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_68_eta_1m1_2p5_4m2_17p1_34m1_68p2_old_408_1_first_coeffs :
    first_coeffs 100 cuspForm_68_eta_1m1_2p5_4m2_17p1_34m1_68p2_old_408_1 =
    [0, 0, 0, 0, 0, 1, 1, -3, -2, 2, -1, 0, 1, 2, 4, -2, 0, -1, -2, 2,
     -1, 0, -3, -3, 1, 2, -2, 2, 4, -3, 0, -3, 2, -2, 1, 6, -2, 3, 0, 2,
     3, 2, -4, 0, -3, -7, 2, 0, 1, -4, 2, 0, -2, -2, -2, -2, -4, 0, 3, 8,
     0, 3, 4, 3, -4, -6, 6, 2, 1, 0, -4, 1, 4, 4, 1, 4, 0, -4, 2, -7,
     -1, -6, -6, 0, -4, 1, -2, 2, -3, -4, 3, 0, 2, 4, 0, 0, 1, 2, 0, 2] := by
  eta_coeff

end WeightTwoCusps
