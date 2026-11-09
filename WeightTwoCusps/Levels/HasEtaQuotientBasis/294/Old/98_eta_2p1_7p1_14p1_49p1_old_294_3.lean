module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«98».New.«98_eta_2p1_7p1_14p1_49p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 294

The eta expression is `η(6z) η(21z) η(42z) η(147z)`; see
[the local level table](../../TABLE.md#level-294).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_98_eta_2p1_7p1_14p1_49p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z) η(21z) η(42z) η(147z)` at level 294. -/
abbrev cuspForm_98_eta_2p1_7p1_14p1_49p1_old_294_3 : gamma0CuspForms 294 :=
  gamma0Rescale cuspForm_98_eta_2p1_7p1_14p1_49p1 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_98_eta_2p1_7p1_14p1_49p1_old_294_3_eq_eta :
    cuspForm_98_eta_2p1_7p1_14p1_49p1_old_294_3 =
      etaQuotientCuspForm 294 sparse![294; 5 => 1, 20 => 1, 41 => 1, 146 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_98_eta_2p1_7p1_14p1_49p1_old_294_3_first_coeffs :
    first_coeffs 100 cuspForm_98_eta_2p1_7p1_14p1_49p1_old_294_3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0,
     0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 1,
     0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 2, 0, 0,
     -1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0,
     0, -3, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, -1] := by
  eta_coeff

end WeightTwoCusps
