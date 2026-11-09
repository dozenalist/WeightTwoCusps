module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 216

The eta expression is `η(z)^(-2) η(2z) η(3z)^5 η(4z)^2 η(6z)^(-4) η(8z)^(-1) η(9z)^(-1) η(12z)^4 η(18z) η(24z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^5 η(4z)^2 η(6z)^(-4) η(8z)^(-1) η(9z)^(-1) η(12z)^4 η(18z) η(24z)^(-1)` at level 216. -/
abbrev cuspForm_216_eta_1m2_2p1_3p5_4p2_6m4_8m1_9m1_12p4_18p1_24m1 : gamma0CuspForms 216 :=
  etaQuotientCuspForm 216 sparse![216; 0 => -2, 1 => 1, 2 => 5, 3 => 2, 5 => -4, 7 => -1, 8 => -1, 11 => 4, 17 => 1, 23 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_216_eta_1m2_2p1_3p5_4p2_6m4_8m1_9m1_12p4_18p1_24m1_first_coeffs :
    first_coeffs 100 cuspForm_216_eta_1m2_2p1_3p5_4p2_6m4_8m1_9m1_12p4_18p1_24m1 =
    [0, 1, 2, 4, 3, 2, 0, 1, 6, 8, 9, 2, 0, 0, 4, 4, 3, -2, 0, 2,
     0, 0, -9, 2, 0, 0, -2, -8, -3, 0, 0, -1, -12, -8, 0, -6, 0, -2, -8, -8,
     -9, 0, 0, -6, 0, -16, -18, -6, 0, -2, -10, -4, -12, -4, 0, -7, -6, -16, 18, 2,
     0, 0, -8, 0, 3, 2, 0, 2, 0, 16, -9, 4, 0, -3, 10, -4, 6, -6, 0, 12,
     0, 8, -18, 4, 0, 4, 16, -12, 9, 6, 0, 8, 0, 32, 18, -2, 0, -1, 12, 32] := by
  eta_coeff

end WeightTwoCusps
