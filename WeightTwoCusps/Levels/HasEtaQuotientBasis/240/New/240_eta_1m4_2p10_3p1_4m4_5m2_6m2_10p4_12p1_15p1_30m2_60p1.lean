module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(5z)^(-2) η(6z)^(-2) η(10z)^4 η(12z) η(15z) η(30z)^(-2) η(60z)`; see
[the local level table](../../TABLE.md#level-240).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(5z)^(-2) η(6z)^(-2) η(10z)^4 η(12z) η(15z) η(30z)^(-2) η(60z)` at level 240. -/
abbrev cuspForm_240_eta_1m4_2p10_3p1_4m4_5m2_6m2_10p4_12p1_15p1_30m2_60p1 : gamma0CuspForms 240 :=
  etaQuotientCuspForm 240 sparse![240; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 4 => -2, 5 => -2, 9 => 4, 11 => 1, 14 => 1, 29 => -2, 59 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m4_2p10_3p1_4m4_5m2_6m2_10p4_12p1_15p1_30m2_60p1_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m4_2p10_3p1_4m4_5m2_6m2_10p4_12p1_15p1_30m2_60p1 =
    [0, 0, 1, 4, 4, -1, 0, 6, 9, 8, -2, 2, 13, 2, 2, -1, 0, 14, -3, 4,
     -1, -14, 10, -4, 6, 0, -20, 4, -10, -2, -3, -20, -3, 6, 8, -10, -20, -2, 16, 2,
     -6, 0, 6, 4, -6, -5, -8, 8, -15, 0, 1, -30, 2, -30, 0, 2, -30, 4, -8, 10,
     -16, -28, 4, 2, -12, -12, 6, 0, 18, -12, -10, 12, 9, 28, 0, 4, -4, 8, -18, -4,
     15, -16, 18, -32, 14, -4, -32, 18, -6, 12, -6, -4, 0, 28, 4, -12, 18, 8, 33, -6] := by
  eta_coeff

end WeightTwoCusps
