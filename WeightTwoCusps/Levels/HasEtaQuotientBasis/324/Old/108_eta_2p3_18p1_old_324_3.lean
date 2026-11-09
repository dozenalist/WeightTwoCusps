module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«108».New.«108_eta_2p3_18p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 324

The eta expression is `η(6z)^3 η(54z)`; see
[the local level table](../../TABLE.md#level-324).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_108_eta_2p3_18p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z)^3 η(54z)` at level 324. -/
abbrev cuspForm_108_eta_2p3_18p1_old_324_3 : gamma0CuspForms 324 :=
  gamma0Rescale cuspForm_108_eta_2p3_18p1 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_108_eta_2p3_18p1_old_324_3_eq_eta :
    cuspForm_108_eta_2p3_18p1_old_324_3 =
      etaQuotientCuspForm 324 sparse![324; 5 => 3, 53 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_108_eta_2p3_18p1_old_324_3_first_coeffs :
    first_coeffs 100 cuspForm_108_eta_2p3_18p1_old_324_3 =
    [0, 0, 0, 1, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -7,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0,
     0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -5, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
