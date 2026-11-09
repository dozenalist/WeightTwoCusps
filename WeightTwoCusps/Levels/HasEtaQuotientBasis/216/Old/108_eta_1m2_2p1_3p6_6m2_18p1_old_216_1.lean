module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«108».New.«108_eta_1m2_2p1_3p6_6m2_18p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 216

The eta expression is `η(z)^(-2) η(2z) η(3z)^6 η(6z)^(-2) η(18z)`; see
[the local level table](../../TABLE.md#level-216).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_108_eta_1m2_2p1_3p6_6m2_18p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^6 η(6z)^(-2) η(18z)` at level 216. -/
abbrev cuspForm_108_eta_1m2_2p1_3p6_6m2_18p1_old_216_1 : gamma0CuspForms 216 :=
  gamma0RescaleToLevel cuspForm_108_eta_1m2_2p1_3p6_6m2_18p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_108_eta_1m2_2p1_3p6_6m2_18p1_old_216_1_eq_eta :
    cuspForm_108_eta_1m2_2p1_3p6_6m2_18p1_old_216_1 =
      etaQuotientCuspForm 216 sparse![216; 0 => -2, 1 => 1, 2 => 6, 5 => -2, 17 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_108_eta_1m2_2p1_3p6_6m2_18p1_old_216_1_first_coeffs :
    first_coeffs 100 cuspForm_108_eta_1m2_2p1_3p6_6m2_18p1_old_216_1 =
    [0, 1, 2, 4, 2, 2, 0, 3, 2, 0, 0, -2, 0, -3, -2, 0, -4, 0, 0, -3,
     -6, -16, 0, -4, 0, -5, -8, 0, -2, 4, 0, -4, 2, 0, 0, -2, 0, 3, 4, 8,
     0, -4, 0, 8, 6, 0, 0, 4, 0, 10, 8, 0, 10, 6, 0, 0, -2, 32, 0, 8,
     0, -9, 10, 0, 8, -8, 0, 9, 0, 0, 0, 0, 0, 9, 4, -20, -14, 2, 0, -3,
     -6, 0, 0, -2, 0, 0, -20, 0, 0, -12, 0, -25, 12, -16, 0, 4, 0, -3, -12, 0] := by
  eta_coeff

end WeightTwoCusps
