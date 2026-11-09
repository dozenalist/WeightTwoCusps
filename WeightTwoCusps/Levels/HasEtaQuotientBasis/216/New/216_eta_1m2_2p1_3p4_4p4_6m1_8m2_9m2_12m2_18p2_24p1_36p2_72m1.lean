module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 216

The eta expression is `η(z)^(-2) η(2z) η(3z)^4 η(4z)^4 η(6z)^(-1) η(8z)^(-2) η(9z)^(-2) η(12z)^(-2) η(18z)^2 η(24z) η(36z)^2 η(72z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^4 η(4z)^4 η(6z)^(-1) η(8z)^(-2) η(9z)^(-2) η(12z)^(-2) η(18z)^2 η(24z) η(36z)^2 η(72z)^(-1)` at level 216. -/
abbrev cuspForm_216_eta_1m2_2p1_3p4_4p4_6m1_8m2_9m2_12m2_18p2_24p1_36p2_72m1 : gamma0CuspForms 216 :=
  etaQuotientCuspForm 216 sparse![216; 0 => -2, 1 => 1, 2 => 4, 3 => 4, 5 => -1, 7 => -2, 8 => -2, 11 => -2, 17 => 2, 23 => 1, 35 => 2, 71 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_216_eta_1m2_2p1_3p4_4p4_6m1_8m2_9m2_12m2_18p2_24p1_36p2_72m1_first_coeffs :
    first_coeffs 100 cuspForm_216_eta_1m2_2p1_3p4_4p4_6m1_8m2_9m2_12m2_18p2_24p1_36p2_72m1 =
    [0, 1, 2, 4, 4, 2, 0, -5, -2, -4, 0, 2, 0, 9, -2, 4, -8, -8, 0, -7,
     6, -12, 0, -4, 0, 3, -8, 4, -4, 12, 0, -4, -2, -8, 0, -6, 0, 7, 4, 4,
     0, -12, 0, 0, -6, 8, 0, 12, 0, -14, 8, -4, 20, 14, 0, 8, 2, 20, 0, 8,
     0, 3, 10, 0, 16, -16, 0, 5, 0, 16, 0, -8, 0, -15, 4, -16, -28, 18, 0, 21,
     6, -4, 0, -14, 0, -8, -20, -12, 0, -12, 0, 11, -12, -4, 0, 4, 0, -19, -12, -16] := by
  eta_coeff

end WeightTwoCusps
