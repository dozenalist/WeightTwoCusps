module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«68».New.«68_eta_1m1_2p2_4p1_17p1_34p2_68m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 340

The eta expression is `η(5z)^(-1) η(10z)^2 η(20z) η(85z) η(170z)^2 η(340z)^(-1)`; see
[the local level table](../../TABLE.md#level-340).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(5z)` of `cuspForm_68_eta_1m1_2p2_4p1_17p1_34p2_68m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(5z)^(-1) η(10z)^2 η(20z) η(85z) η(170z)^2 η(340z)^(-1)` at level 340. -/
abbrev cuspForm_68_eta_1m1_2p2_4p1_17p1_34p2_68m1_old_340_5 : gamma0CuspForms 340 :=
  gamma0Rescale cuspForm_68_eta_1m1_2p2_4p1_17p1_34p2_68m1 5

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_68_eta_1m1_2p2_4p1_17p1_34p2_68m1_old_340_5_eq_eta :
    cuspForm_68_eta_1m1_2p2_4p1_17p1_34p2_68m1_old_340_5 =
      etaQuotientCuspForm 340 sparse![340; 4 => -1, 9 => 2, 19 => 1, 84 => 1, 169 => 2, 339 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_68_eta_1m1_2p2_4p1_17p1_34p2_68m1_old_340_5_first_coeffs :
    first_coeffs 100 cuspForm_68_eta_1m1_2p2_4p1_17p1_34p2_68m1_old_340_5 =
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0,
     -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -2, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
