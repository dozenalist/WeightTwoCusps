module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 216

The eta expression is `η(z)^(-4) η(2z)^6 η(3z)^7 η(4z)^(-2) η(6z)^(-5) η(9z)^(-1) η(12z)^2 η(18z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^6 η(3z)^7 η(4z)^(-2) η(6z)^(-5) η(9z)^(-1) η(12z)^2 η(18z)` at level 216. -/
abbrev cuspForm_216_eta_1m4_2p6_3p7_4m2_6m5_9m1_12p2_18p1 : gamma0CuspForms 216 :=
  etaQuotientCuspForm 216 sparse![216; 0 => -4, 1 => 6, 2 => 7, 3 => -2, 5 => -5, 8 => -1, 11 => 2, 17 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_216_eta_1m4_2p6_3p7_4m2_6m5_9m1_12p2_18p1_first_coeffs :
    first_coeffs 100 cuspForm_216_eta_1m4_2p6_3p7_4m2_6m5_9m1_12p2_18p1 =
    [0, 1, 4, 8, 9, 4, 0, 3, 12, 16, 9, 4, 0, 4, 8, 8, 9, -4, 0, 2,
     0, 0, -9, 4, 0, -4, -4, -16, -9, 0, 0, -7, -24, -16, 0, -12, 0, -6, -16, -16,
     -27, 0, 0, -2, 0, -32, -18, -12, 0, 2, -20, -8, -36, -8, 0, -5, -12, -32, 18, 4,
     0, -8, -16, 0, 9, 4, 0, -10, 0, 32, -9, 8, 0, 1, 20, -8, 18, -12, 0, 16,
     0, 16, -18, 8, 0, 8, 32, -24, 27, 12, 0, 12, 0, 64, 18, -4, 0, -1, 24, 64] := by
  eta_coeff

end WeightTwoCusps
