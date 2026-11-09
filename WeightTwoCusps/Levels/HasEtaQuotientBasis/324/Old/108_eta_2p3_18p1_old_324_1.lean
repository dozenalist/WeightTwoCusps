module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«108».New.«108_eta_2p3_18p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 324

The eta expression is `η(2z)^3 η(18z)`; see
[the local level table](../../TABLE.md#level-324).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_108_eta_2p3_18p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^3 η(18z)` at level 324. -/
abbrev cuspForm_108_eta_2p3_18p1_old_324_1 : gamma0CuspForms 324 :=
  gamma0RescaleToLevel cuspForm_108_eta_2p3_18p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_108_eta_2p3_18p1_old_324_1_eq_eta :
    cuspForm_108_eta_2p3_18p1_old_324_1 =
      etaQuotientCuspForm 324 sparse![324; 1 => 3, 17 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_108_eta_2p3_18p1_old_324_1_first_coeffs :
    first_coeffs 100 cuspForm_108_eta_2p3_18p1_old_324_1 =
    [0, 1, 0, -3, 0, 0, 0, 5, 0, 0, 0, 0, 0, -7, 0, 0, 0, 0, 0, -1,
     0, 12, 0, 0, 0, -5, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, -1, 0, -6,
     0, 0, 0, 8, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, -24, 0, 0,
     0, -13, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 17, 0, 15, 0, 0, 0, -13,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -35, 0, 12, 0, 0, 0, 5, 0, 0] := by
  eta_coeff

end WeightTwoCusps
