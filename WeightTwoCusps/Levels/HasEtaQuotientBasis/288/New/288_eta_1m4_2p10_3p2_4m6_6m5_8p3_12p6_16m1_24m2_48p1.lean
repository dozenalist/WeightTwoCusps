module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 288

The eta expression is `η(z)^(-4) η(2z)^10 η(3z)^2 η(4z)^(-6) η(6z)^(-5) η(8z)^3 η(12z)^6 η(16z)^(-1) η(24z)^(-2) η(48z)`; see
[the local level table](../../TABLE.md#level-288).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^10 η(3z)^2 η(4z)^(-6) η(6z)^(-5) η(8z)^3 η(12z)^6 η(16z)^(-1) η(24z)^(-2) η(48z)` at level 288. -/
abbrev cuspForm_288_eta_1m4_2p10_3p2_4m6_6m5_8p3_12p6_16m1_24m2_48p1 : gamma0CuspForms 288 :=
  etaQuotientCuspForm 288 sparse![288; 0 => -4, 1 => 10, 2 => 2, 3 => -6, 5 => -5, 7 => 3, 11 => 6, 15 => -1, 23 => -2, 47 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_288_eta_1m4_2p10_3p2_4m6_6m5_8p3_12p6_16m1_24m2_48p1_first_coeffs :
    first_coeffs 100 cuspForm_288_eta_1m4_2p10_3p2_4m6_6m5_8p3_12p6_16m1_24m2_48p1 =
    [0, 0, 1, 4, 4, -2, -2, 8, 12, 4, -2, 4, 8, 4, 6, 8, 0, -8, -2, 8,
     4, -4, -4, 0, 0, 0, 4, 4, 0, 6, 4, -8, 0, 4, 2, -8, -8, 0, -14, -8,
     0, 4, 0, -8, -8, -4, 8, 8, 0, -8, -7, -24, -8, 2, -2, -16, -48, -4, 6, -4,
     -16, -8, 10, -16, 0, 20, 8, -8, -4, 0, 0, -16, 0, 0, -18, -4, -16, -4, 4, -8,
     0, -8, -6, 12, 0, 4, -10, 8, 0, -12, 4, -16, 16, 4, 0, -8, 0, 16, 17, 16] := by
  eta_coeff

end WeightTwoCusps
