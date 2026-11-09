module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 288

The eta expression is `η(z)^(-5) η(2z)^12 η(3z)^3 η(4z)^(-6) η(6z)^(-6) η(8z) η(12z)^6 η(24z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-5) η(2z)^12 η(3z)^3 η(4z)^(-6) η(6z)^(-6) η(8z) η(12z)^6 η(24z)^(-1)` at level 288. -/
abbrev cuspForm_288_eta_1m5_2p12_3p3_4m6_6m6_8p1_12p6_24m1 : gamma0CuspForms 288 :=
  etaQuotientCuspForm 288 sparse![288; 0 => -5, 1 => 12, 2 => 3, 3 => -6, 5 => -6, 7 => 1, 11 => 6, 23 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_288_eta_1m5_2p12_3p3_4m6_6m6_8p1_12p6_24m1_first_coeffs :
    first_coeffs 100 cuspForm_288_eta_1m5_2p12_3p3_4m6_6m6_8p1_12p6_24m1 =
    [0, 1, 5, 8, 2, -5, 2, 16, 18, 6, 2, 8, 4, 6, 18, 16, 0, -13, 2, 16,
     2, 0, 4, 0, 0, -1, 8, 8, 0, 11, -4, -16, 0, 0, -2, -16, -4, -2, -34, -16,
     0, 7, 0, -16, -4, -12, -8, 16, 0, -7, -23, -48, -4, -1, 2, -32, -72, 0, -6, -8,
     -8, -10, 14, -32, 0, 42, -8, -16, -2, 0, 0, -32, 0, -6, -42, -8, -8, 0, -4, -16,
     0, -18, 6, 24, 0, -4, -38, 16, 0, -29, -4, -32, 8, 0, 0, -16, 0, 18, 37, 32] := by
  eta_coeff

end WeightTwoCusps
