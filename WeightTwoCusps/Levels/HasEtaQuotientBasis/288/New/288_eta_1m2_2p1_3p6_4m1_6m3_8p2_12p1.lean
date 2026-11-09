module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 288

The eta expression is `η(z)^(-2) η(2z) η(3z)^6 η(4z)^(-1) η(6z)^(-3) η(8z)^2 η(12z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^6 η(4z)^(-1) η(6z)^(-3) η(8z)^2 η(12z)` at level 288. -/
abbrev cuspForm_288_eta_1m2_2p1_3p6_4m1_6m3_8p2_12p1 : gamma0CuspForms 288 :=
  etaQuotientCuspForm 288 sparse![288; 0 => -2, 1 => 1, 2 => 6, 3 => -1, 5 => -3, 7 => 2, 11 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_288_eta_1m2_2p1_3p6_4m1_6m3_8p2_12p1_first_coeffs :
    first_coeffs 100 cuspForm_288_eta_1m2_2p1_3p6_4m1_6m3_8p2_12p1 =
    [0, 1, 2, 4, 2, 3, 2, 8, 6, 6, 2, 4, 4, 6, 6, 8, 0, 3, 2, 8,
     2, 0, 4, 0, 0, -1, 2, 4, 0, 3, -4, -8, 0, 0, -2, -8, -4, -2, -10, -8,
     0, -9, 0, -8, -4, -12, -8, 8, 0, -7, -8, -24, -4, -9, 2, -16, -24, 0, -6, -4,
     -8, -10, 2, -16, 0, -6, -8, -8, -2, 0, 0, -16, 0, -6, -12, -4, -8, 0, -4, -8,
     0, -18, 6, 12, 0, -4, -14, 8, 0, 3, -4, -16, 8, 0, 0, -8, 0, 18, 10, 16] := by
  eta_coeff

end WeightTwoCusps
