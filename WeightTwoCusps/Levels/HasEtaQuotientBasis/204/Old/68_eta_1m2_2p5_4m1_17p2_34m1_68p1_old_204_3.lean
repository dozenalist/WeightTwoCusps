module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«68».New.«68_eta_1m2_2p5_4m1_17p2_34m1_68p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 204

The eta expression is `η(3z)^(-2) η(6z)^5 η(12z)^(-1) η(51z)^2 η(102z)^(-1) η(204z)`; see
[the local level table](../../TABLE.md#level-204).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_68_eta_1m2_2p5_4m1_17p2_34m1_68p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-2) η(6z)^5 η(12z)^(-1) η(51z)^2 η(102z)^(-1) η(204z)` at level 204. -/
abbrev cuspForm_68_eta_1m2_2p5_4m1_17p2_34m1_68p1_old_204_3 : gamma0CuspForms 204 :=
  gamma0Rescale cuspForm_68_eta_1m2_2p5_4m1_17p2_34m1_68p1 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_68_eta_1m2_2p5_4m1_17p2_34m1_68p1_old_204_3_eq_eta :
    cuspForm_68_eta_1m2_2p5_4m1_17p2_34m1_68p1_old_204_3 =
      etaQuotientCuspForm 204 sparse![204; 2 => -2, 5 => 5, 11 => -1, 50 => 2, 101 => -1, 203 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_68_eta_1m2_2p5_4m1_17p2_34m1_68p1_old_204_3_first_coeffs :
    first_coeffs 100 cuspForm_68_eta_1m2_2p5_4m1_17p2_34m1_68p1_old_204_3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0,
     0, 1, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, -2, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0,
     -4, 0, 0, -4, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0,
     0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 6, 0, 0, 4] := by
  eta_coeff

end WeightTwoCusps
