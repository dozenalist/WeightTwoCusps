module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 216

The eta expression is `η(z)^(-3) η(2z)^5 η(3z) η(4z)^3 η(8z)^(-2) η(12z)^(-2) η(18z)^(-1) η(24z) η(36z)^3 η(72z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^5 η(3z) η(4z)^3 η(8z)^(-2) η(12z)^(-2) η(18z)^(-1) η(24z) η(36z)^3 η(72z)^(-1)` at level 216. -/
abbrev cuspForm_216_eta_1m3_2p5_3p1_4p3_8m2_12m2_18m1_24p1_36p3_72m1 : gamma0CuspForms 216 :=
  etaQuotientCuspForm 216 sparse![216; 0 => -3, 1 => 5, 2 => 1, 3 => 3, 7 => -2, 11 => -2, 17 => -1, 23 => 1, 35 => 3, 71 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_216_eta_1m3_2p5_3p1_4p3_8m2_12m2_18m1_24p1_36p3_72m1_first_coeffs :
    first_coeffs 100 cuspForm_216_eta_1m3_2p5_3p1_4p3_8m2_12m2_18m1_24p1_36p3_72m1 =
    [0, 1, 3, 4, 6, 5, 0, 1, -3, -4, 0, -7, 0, -3, -3, 4, -12, 4, 0, -1,
     9, -12, 0, -10, 0, 3, -12, 4, -6, 6, 0, -4, -3, -8, 0, -3, 0, -5, 6, 4,
     0, -6, 0, 0, -9, 8, 0, 6, 0, 10, 12, -4, 30, 11, 0, 8, 3, 20, 0, 20,
     0, -9, 15, 0, 24, -16, 0, 11, 0, 16, 0, 4, 0, 9, 6, -16, -42, -3, 0, -9,
     9, -4, 0, 1, 0, -8, -30, -12, 0, -30, 0, -19, -18, -4, 0, 10, 0, 5, -18, -16] := by
  eta_coeff

end WeightTwoCusps
