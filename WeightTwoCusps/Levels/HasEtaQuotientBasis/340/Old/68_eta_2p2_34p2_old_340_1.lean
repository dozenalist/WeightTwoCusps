module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«68».New.«68_eta_2p2_34p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 340

The eta expression is `η(2z)^2 η(34z)^2`; see
[the local level table](../../TABLE.md#level-340).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_68_eta_2p2_34p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^2 η(34z)^2` at level 340. -/
abbrev cuspForm_68_eta_2p2_34p2_old_340_1 : gamma0CuspForms 340 :=
  gamma0RescaleToLevel cuspForm_68_eta_2p2_34p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_68_eta_2p2_34p2_old_340_1_eq_eta :
    cuspForm_68_eta_2p2_34p2_old_340_1 =
      etaQuotientCuspForm 340 sparse![340; 1 => 2, 33 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_68_eta_2p2_34p2_old_340_1_first_coeffs :
    first_coeffs 100 cuspForm_68_eta_2p2_34p2_old_340_1 =
    [0, 0, 0, 1, 0, -2, 0, -1, 0, 2, 0, 1, 0, 2, 0, -2, 0, 0, 0, -2,
     0, -2, 0, 1, 0, 0, 0, 0, 0, 2, 0, 3, 0, -2, 0, 2, 0, -2, 0, 4,
     0, 0, 0, -6, 0, -2, 0, -4, 0, 2, 0, -1, 0, 4, 0, 6, 0, 0, 0, -2,
     0, 2, 0, -3, 0, -4, 0, 4, 0, -2, 0, -3, 0, 0, 0, 7, 0, 2, 0, -3,
     0, -2, 0, 2, 0, 2, 0, 2, 0, -2, 0, -4, 0, 2, 0, -4, 0, -4, 0, -5] := by
  eta_coeff

end WeightTwoCusps
