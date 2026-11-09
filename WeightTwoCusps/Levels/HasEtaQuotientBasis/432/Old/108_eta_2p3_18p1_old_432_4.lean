module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«108».New.«108_eta_2p3_18p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 432

The eta expression is `η(8z)^3 η(72z)`; see
[the local level table](../../TABLE.md#level-432).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_108_eta_2p3_18p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(8z)^3 η(72z)` at level 432. -/
abbrev cuspForm_108_eta_2p3_18p1_old_432_4 : gamma0CuspForms 432 :=
  gamma0Rescale cuspForm_108_eta_2p3_18p1 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_108_eta_2p3_18p1_old_432_4_eq_eta :
    cuspForm_108_eta_2p3_18p1_old_432_4 =
      etaQuotientCuspForm 432 sparse![432; 7 => 3, 71 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_108_eta_2p3_18p1_old_432_4_first_coeffs :
    first_coeffs 100 cuspForm_108_eta_2p3_18p1_old_432_4 =
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -7, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
