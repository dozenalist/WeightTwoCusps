module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 216

The eta expression is `η(z)^(-3) η(2z)^6 η(3z)^3 η(4z)^(-1) η(6z)^(-4) η(8z)^(-1) η(9z)^(-2) η(12z) η(18z)^4 η(24z)^2 η(72z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z)^3 η(4z)^(-1) η(6z)^(-4) η(8z)^(-1) η(9z)^(-2) η(12z) η(18z)^4 η(24z)^2 η(72z)^(-1)` at level 216. -/
abbrev cuspForm_216_eta_1m3_2p6_3p3_4m1_6m4_8m1_9m2_12p1_18p4_24p2_72m1 : gamma0CuspForms 216 :=
  etaQuotientCuspForm 216 sparse![216; 0 => -3, 1 => 6, 2 => 3, 3 => -1, 5 => -4, 7 => -1, 8 => -2, 11 => 1, 17 => 4, 23 => 2, 71 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_216_eta_1m3_2p6_3p3_4m1_6m4_8m1_9m2_12p1_18p4_24p2_72m1_first_coeffs :
    first_coeffs 100 cuspForm_216_eta_1m3_2p6_3p3_4m1_6m4_8m1_9m2_12p1_18p4_24p2_72m1 =
    [0, 1, 3, 3, 1, -2, -3, 1, 4, 6, 3, -2, 0, 0, 3, 3, 1, 2, 0, 2,
     0, 0, -3, -2, 0, 0, 3, -6, -1, 0, 0, -1, -8, -6, 0, 6, 0, -2, -15, -6,
     -3, 0, 12, -6, 0, -12, -6, 6, 0, -2, -15, -3, -4, 4, 0, -7, -4, -12, 6, -2,
     0, 0, -12, 0, 1, -2, 0, 2, 0, 12, -3, -4, 0, -3, 21, -3, 2, 6, -6, 12,
     0, 6, -6, -4, 0, 4, 24, -9, 3, -6, 0, 8, 0, 24, 6, 2, 0, -1, 6, 24] := by
  eta_coeff

end WeightTwoCusps
