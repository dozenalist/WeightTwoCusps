module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 216

The eta expression is `η(z)^(-6) η(2z)^13 η(3z)^5 η(4z)^(-5) η(6z)^(-6) η(9z)^(-1) η(12z)^3 η(18z)`; see
[the local level table](../../TABLE.md#level-216).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-6) η(2z)^13 η(3z)^5 η(4z)^(-5) η(6z)^(-6) η(9z)^(-1) η(12z)^3 η(18z)` at level 216. -/
abbrev cuspForm_216_eta_1m6_2p13_3p5_4m5_6m6_9m1_12p3_18p1 : gamma0CuspForms 216 :=
  etaQuotientCuspForm 216 sparse![216; 0 => -6, 1 => 13, 2 => 5, 3 => -5, 5 => -6, 8 => -1, 11 => 3, 17 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_216_eta_1m6_2p13_3p5_4m5_6m6_9m1_12p3_18p1_first_coeffs :
    first_coeffs 100 cuspForm_216_eta_1m6_2p13_3p5_4m5_6m6_9m1_12p3_18p1 =
    [0, 1, 6, 14, 15, 4, -6, 3, 24, 28, 15, 4, 0, 4, 6, 14, 15, -4, 0, 2,
     0, 0, -15, 4, 0, -4, 6, -28, -15, 0, 0, -7, -48, -28, 0, -12, 0, -6, -30, -28,
     -45, 0, 24, -2, 0, -56, -30, -12, 0, 2, -30, -14, -60, -8, 0, -5, -24, -56, 30, 4,
     0, -8, -24, 0, 15, 4, 0, -10, 0, 56, -15, 8, 0, 1, 42, -14, 30, -12, -12, 16,
     0, 28, -30, 8, 0, 8, 48, -42, 45, 12, 0, 12, 0, 112, 30, -4, 0, -1, 12, 112] := by
  eta_coeff

end WeightTwoCusps
