module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«68».New.«68_eta_2p2_34p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 408

The eta expression is `η(6z)^2 η(102z)^2`; see
[the local level table](../../TABLE.md#level-408).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_68_eta_2p2_34p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z)^2 η(102z)^2` at level 408. -/
abbrev cuspForm_68_eta_2p2_34p2_old_408_3 : gamma0CuspForms 408 :=
  gamma0RescaleToLevel cuspForm_68_eta_2p2_34p2 3 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_68_eta_2p2_34p2_old_408_3_eq_eta :
    cuspForm_68_eta_2p2_34p2_old_408_3 =
      etaQuotientCuspForm 408 sparse![408; 5 => 2, 101 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_68_eta_2p2_34p2_old_408_3_first_coeffs :
    first_coeffs 100 cuspForm_68_eta_2p2_34p2_old_408_3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0,
     0, -1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2,
     0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0,
     0, 0, 0, -2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, -2] := by
  eta_coeff

end WeightTwoCusps
