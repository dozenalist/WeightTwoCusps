module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«108».New.«108_eta_1m3_2p5_3p4_4m1_6m2_9m1_18p1_36p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 216

The eta expression is `η(z)^(-3) η(2z)^5 η(3z)^4 η(4z)^(-1) η(6z)^(-2) η(9z)^(-1) η(18z) η(36z)`; see
[the local level table](../../TABLE.md#level-216).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_108_eta_1m3_2p5_3p4_4m1_6m2_9m1_18p1_36p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^5 η(3z)^4 η(4z)^(-1) η(6z)^(-2) η(9z)^(-1) η(18z) η(36z)` at level 216. -/
abbrev cuspForm_108_eta_1m3_2p5_3p4_4m1_6m2_9m1_18p1_36p1_old_216_1 : gamma0CuspForms 216 :=
  gamma0RescaleToLevel cuspForm_108_eta_1m3_2p5_3p4_4m1_6m2_9m1_18p1_36p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_108_eta_1m3_2p5_3p4_4m1_6m2_9m1_18p1_36p1_old_216_1_eq_eta :
    cuspForm_108_eta_1m3_2p5_3p4_4m1_6m2_9m1_18p1_36p1_old_216_1 =
      etaQuotientCuspForm 216 sparse![216; 0 => -3, 1 => 5, 2 => 4, 3 => -1, 5 => -2, 8 => -1, 17 => 1, 35 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_108_eta_1m3_2p5_3p4_4m1_6m2_9m1_18p1_36p1_old_216_1_first_coeffs :
    first_coeffs 100 cuspForm_108_eta_1m3_2p5_3p4_4m1_6m2_9m1_18p1_36p1_old_216_1 =
    [0, 0, 1, 3, 4, 3, 0, 0, 1, 0, 0, -3, 0, 0, -1, 0, -8, 0, 0, 0,
     -3, -12, 0, -6, 0, 0, -4, 0, -4, 6, 0, 0, 1, 0, 0, -3, 0, 0, 2, 6,
     0, -6, 0, 0, 3, 0, 0, 6, 0, 0, 4, 0, 20, 9, 0, 0, -1, 24, 0, 12,
     0, 0, 5, 0, 16, -12, 0, 0, 0, 0, 0, 0, 0, 0, 2, -15, -28, 3, 0, 0,
     -3, 0, 0, -3, 0, 0, -10, 0, 0, -18, 0, 0, 6, -12, 0, 6, 0, 0, -6, 0] := by
  eta_coeff

end WeightTwoCusps
