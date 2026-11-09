module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«68».New.«68_eta_1m1_2p2_4p1_17p1_34p2_68m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 408

The eta expression is `η(6z)^(-1) η(12z)^2 η(24z) η(102z) η(204z)^2 η(408z)^(-1)`; see
[the local level table](../../TABLE.md#level-408).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(6z)` of `cuspForm_68_eta_1m1_2p2_4p1_17p1_34p2_68m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z)^(-1) η(12z)^2 η(24z) η(102z) η(204z)^2 η(408z)^(-1)` at level 408. -/
abbrev cuspForm_68_eta_1m1_2p2_4p1_17p1_34p2_68m1_old_408_6 : gamma0CuspForms 408 :=
  gamma0Rescale cuspForm_68_eta_1m1_2p2_4p1_17p1_34p2_68m1 6

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_68_eta_1m1_2p2_4p1_17p1_34p2_68m1_old_408_6_eq_eta :
    cuspForm_68_eta_1m1_2p2_4p1_17p1_34p2_68m1_old_408_6 =
      etaQuotientCuspForm 408 sparse![408; 5 => -1, 11 => 2, 23 => 1, 101 => 1, 203 => 2, 407 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_68_eta_1m1_2p2_4p1_17p1_34p2_68m1_old_408_6_first_coeffs :
    first_coeffs 100 cuspForm_68_eta_1m1_2p2_4p1_17p1_34p2_68m1_old_408_6 =
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0,
     -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
