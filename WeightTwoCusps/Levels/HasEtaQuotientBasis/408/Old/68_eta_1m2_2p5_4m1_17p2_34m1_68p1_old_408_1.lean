module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«68».New.«68_eta_1m2_2p5_4m1_17p2_34m1_68p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 408

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-1) η(17z)^2 η(34z)^(-1) η(68z)`; see
[the local level table](../../TABLE.md#level-408).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_68_eta_1m2_2p5_4m1_17p2_34m1_68p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-1) η(17z)^2 η(34z)^(-1) η(68z)` at level 408. -/
abbrev cuspForm_68_eta_1m2_2p5_4m1_17p2_34m1_68p1_old_408_1 : gamma0CuspForms 408 :=
  gamma0RescaleToLevel cuspForm_68_eta_1m2_2p5_4m1_17p2_34m1_68p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_68_eta_1m2_2p5_4m1_17p2_34m1_68p1_old_408_1_eq_eta :
    cuspForm_68_eta_1m2_2p5_4m1_17p2_34m1_68p1_old_408_1 =
      etaQuotientCuspForm 408 sparse![408; 0 => -2, 1 => 5, 3 => -1, 16 => 2, 33 => -1, 67 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_68_eta_1m2_2p5_4m1_17p2_34m1_68p1_old_408_1_first_coeffs :
    first_coeffs 100 cuspForm_68_eta_1m2_2p5_4m1_17p2_34m1_68p1_old_408_1 =
    [0, 0, 0, 1, 2, 0, 0, 1, -2, 0, 0, -3, 0, 0, 0, -2, -2, 0, 0, 2,
     -4, -4, 0, -1, 0, 4, 0, 0, 8, 0, 0, 1, 6, 4, 0, 2, -6, 4, 0, 4,
     4, -4, 0, -2, 0, -4, 0, 0, 0, -4, 0, -1, -4, 4, 0, -2, -8, -4, 0, 2,
     0, 0, 0, -1, -2, -4, 0, 0, 2, 0, 0, -1, 6, 0, 0, -1, -8, 8, 0, -5,
     4, 4, 0, -2, 0, 0, 0, 2, 0, 4, 0, 0, 8, 0, 0, 4, 0, -4, 0, -1] := by
  eta_coeff

end WeightTwoCusps
