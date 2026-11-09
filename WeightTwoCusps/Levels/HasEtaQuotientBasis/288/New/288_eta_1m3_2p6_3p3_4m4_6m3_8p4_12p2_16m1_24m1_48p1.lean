module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 288

The eta expression is `η(z)^(-3) η(2z)^6 η(3z)^3 η(4z)^(-4) η(6z)^(-3) η(8z)^4 η(12z)^2 η(16z)^(-1) η(24z)^(-1) η(48z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z)^3 η(4z)^(-4) η(6z)^(-3) η(8z)^4 η(12z)^2 η(16z)^(-1) η(24z)^(-1) η(48z)` at level 288. -/
abbrev cuspForm_288_eta_1m3_2p6_3p3_4m4_6m3_8p4_12p2_16m1_24m1_48p1 : gamma0CuspForms 288 :=
  etaQuotientCuspForm 288 sparse![288; 0 => -3, 1 => 6, 2 => 3, 3 => -4, 5 => -3, 7 => 4, 11 => 2, 15 => -1, 23 => -1, 47 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_288_eta_1m3_2p6_3p3_4m4_6m3_8p4_12p2_16m1_24m1_48p1_first_coeffs :
    first_coeffs 100 cuspForm_288_eta_1m3_2p6_3p3_4m4_6m3_8p4_12p2_16m1_24m1_48p1 =
    [0, 0, 1, 3, 3, 1, 1, 6, 9, 4, 1, 3, 6, 4, 3, 6, 0, -2, 1, 6,
     3, -4, 2, 0, 0, 0, 1, 3, 0, 3, -2, -6, 0, 4, -1, -6, -6, 0, -5, -6,
     0, -2, 0, -6, -6, -4, -4, 6, 0, -8, -4, -18, -6, -1, 1, -12, -36, -4, -3, -3,
     -12, -8, 1, -12, 0, 2, -4, -6, -3, 0, 0, -12, 0, 0, -6, -3, -12, -4, -2, -6,
     0, -8, 3, 9, 0, 4, -7, 6, 0, 0, -2, -12, 12, 4, 0, -6, 0, 16, 5, 12] := by
  eta_coeff

end WeightTwoCusps
