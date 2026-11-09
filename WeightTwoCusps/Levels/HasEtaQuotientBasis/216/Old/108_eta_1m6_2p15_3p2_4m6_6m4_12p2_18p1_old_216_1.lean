module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«108».New.«108_eta_1m6_2p15_3p2_4m6_6m4_12p2_18p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 216

The eta expression is `η(z)^(-6) η(2z)^15 η(3z)^2 η(4z)^(-6) η(6z)^(-4) η(12z)^2 η(18z)`; see
[the local level table](../../TABLE.md#level-216).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_108_eta_1m6_2p15_3p2_4m6_6m4_12p2_18p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-6) η(2z)^15 η(3z)^2 η(4z)^(-6) η(6z)^(-4) η(12z)^2 η(18z)` at level 216. -/
abbrev cuspForm_108_eta_1m6_2p15_3p2_4m6_6m4_12p2_18p1_old_216_1 : gamma0CuspForms 216 :=
  gamma0RescaleToLevel cuspForm_108_eta_1m6_2p15_3p2_4m6_6m4_12p2_18p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_108_eta_1m6_2p15_3p2_4m6_6m4_12p2_18p1_old_216_1_eq_eta :
    cuspForm_108_eta_1m6_2p15_3p2_4m6_6m4_12p2_18p1_old_216_1 =
      etaQuotientCuspForm 216 sparse![216; 0 => -6, 1 => 15, 2 => 2, 3 => -6, 5 => -4, 11 => 2, 17 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_108_eta_1m6_2p15_3p2_4m6_6m4_12p2_18p1_old_216_1_first_coeffs :
    first_coeffs 100 cuspForm_108_eta_1m6_2p15_3p2_4m6_6m4_12p2_18p1_old_216_1 =
    [0, 1, 6, 12, 6, -6, 0, 11, 6, 0, 0, 6, 0, -19, -6, 0, -12, 0, 0, 5,
     -18, -48, 0, 12, 0, -5, -24, 0, -6, -12, 0, -4, 6, 0, 0, 6, 0, -13, 12, 24,
     0, 12, 0, 8, 18, 0, 0, -12, 0, 42, 24, 0, 30, -18, 0, 0, -6, 96, 0, -24,
     0, -25, 30, 0, 24, 24, 0, 17, 0, 0, 0, 0, 0, 41, 12, -60, -42, -6, 0, -43,
     -18, 0, 0, 6, 0, 0, -60, 0, 0, 36, 0, -65, 36, -48, 0, -12, 0, 29, -36, 0] := by
  eta_coeff

end WeightTwoCusps
