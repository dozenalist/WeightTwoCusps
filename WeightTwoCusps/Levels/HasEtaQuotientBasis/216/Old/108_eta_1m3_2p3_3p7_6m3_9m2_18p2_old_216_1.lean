module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«108».New.«108_eta_1m3_2p3_3p7_6m3_9m2_18p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 216

The eta expression is `η(z)^(-3) η(2z)^3 η(3z)^7 η(6z)^(-3) η(9z)^(-2) η(18z)^2`; see
[the local level table](../../TABLE.md#level-216).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_108_eta_1m3_2p3_3p7_6m3_9m2_18p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^3 η(3z)^7 η(6z)^(-3) η(9z)^(-2) η(18z)^2` at level 216. -/
abbrev cuspForm_108_eta_1m3_2p3_3p7_6m3_9m2_18p2_old_216_1 : gamma0CuspForms 216 :=
  gamma0RescaleToLevel cuspForm_108_eta_1m3_2p3_3p7_6m3_9m2_18p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_108_eta_1m3_2p3_3p7_6m3_9m2_18p2_old_216_1_eq_eta :
    cuspForm_108_eta_1m3_2p3_3p7_6m3_9m2_18p2_old_216_1 =
      etaQuotientCuspForm 216 sparse![216; 0 => -3, 1 => 3, 2 => 7, 5 => -3, 8 => -2, 17 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_108_eta_1m3_2p3_3p7_6m3_9m2_18p2_old_216_1_first_coeffs :
    first_coeffs 100 cuspForm_108_eta_1m3_2p3_3p7_6m3_9m2_18p2_old_216_1 =
    [0, 1, 3, 6, 6, 3, 0, -1, 3, 0, 0, -3, 0, 5, -3, 0, -12, 0, 0, -7,
     -9, -24, 0, -6, 0, -5, -12, 0, -6, 6, 0, -4, 3, 0, 0, -3, 0, 11, 6, 12,
     0, -6, 0, 8, 9, 0, 0, 6, 0, -6, 12, 0, 30, 9, 0, 0, -3, 48, 0, 12,
     0, -1, 15, 0, 24, -12, 0, 5, 0, 0, 0, 0, 0, -7, 6, -30, -42, 3, 0, 17,
     -9, 0, 0, -3, 0, 0, -30, 0, 0, -18, 0, -5, 18, -24, 0, 6, 0, -19, -18, 0] := by
  eta_coeff

end WeightTwoCusps
