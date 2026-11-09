module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«108».New.«108_eta_1m4_2p8_3p4_4m3_6m3_12p1_18p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 216

The eta expression is `η(z)^(-4) η(2z)^8 η(3z)^4 η(4z)^(-3) η(6z)^(-3) η(12z) η(18z)`; see
[the local level table](../../TABLE.md#level-216).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_108_eta_1m4_2p8_3p4_4m3_6m3_12p1_18p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^8 η(3z)^4 η(4z)^(-3) η(6z)^(-3) η(12z) η(18z)` at level 216. -/
abbrev cuspForm_108_eta_1m4_2p8_3p4_4m3_6m3_12p1_18p1_old_216_1 : gamma0CuspForms 216 :=
  gamma0RescaleToLevel cuspForm_108_eta_1m4_2p8_3p4_4m3_6m3_12p1_18p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_108_eta_1m4_2p8_3p4_4m3_6m3_12p1_18p1_old_216_1_eq_eta :
    cuspForm_108_eta_1m4_2p8_3p4_4m3_6m3_12p1_18p1_old_216_1 =
      etaQuotientCuspForm 216 sparse![216; 0 => -4, 1 => 8, 2 => 4, 3 => -3, 5 => -3, 11 => 1, 17 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_108_eta_1m4_2p8_3p4_4m3_6m3_12p1_18p1_old_216_1_first_coeffs :
    first_coeffs 100 cuspForm_108_eta_1m4_2p8_3p4_4m3_6m3_12p1_18p1_old_216_1 =
    [0, 1, 4, 6, 4, 0, 0, 5, 4, 0, 0, 0, 0, -7, -4, 0, -8, 0, 0, -1,
     -12, -24, 0, 0, 0, -5, -16, 0, -4, 0, 0, -4, 4, 0, 0, 0, 0, -1, 8, 12,
     0, 0, 0, 8, 12, 0, 0, 0, 0, 18, 16, 0, 20, 0, 0, 0, -4, 48, 0, 0,
     0, -13, 20, 0, 16, 0, 0, 11, 0, 0, 0, 0, 0, 17, 8, -30, -28, 0, 0, -13,
     -12, 0, 0, 0, 0, 0, -40, 0, 0, 0, 0, -35, 24, -24, 0, 0, 0, 5, -24, 0] := by
  eta_coeff

end WeightTwoCusps
