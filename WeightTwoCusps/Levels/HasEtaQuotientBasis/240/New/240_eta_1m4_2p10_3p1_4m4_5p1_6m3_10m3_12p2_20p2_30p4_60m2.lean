module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(5z) η(6z)^(-3) η(10z)^(-3) η(12z)^2 η(20z)^2 η(30z)^4 η(60z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(5z) η(6z)^(-3) η(10z)^(-3) η(12z)^2 η(20z)^2 η(30z)^4 η(60z)^(-2)` at level 240. -/
abbrev cuspForm_240_eta_1m4_2p10_3p1_4m4_5p1_6m3_10m3_12p2_20p2_30p4_60m2 : gamma0CuspForms 240 :=
  etaQuotientCuspForm 240 sparse![240; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 4 => 1, 5 => -3, 9 => -3, 11 => 2, 19 => 2, 29 => 4, 59 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m4_2p10_3p1_4m4_5p1_6m3_10m3_12p2_20p2_30p4_60m2_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m4_2p10_3p1_4m4_5p1_6m3_10m3_12p2_20p2_30p4_60m2 =
    [0, 1, 4, 4, -1, 0, 3, -2, 0, 5, 1, 2, 6, 4, -2, -1, 3, -4, 0, 8,
     2, 2, 6, 4, -1, -3, -2, -4, -2, 8, 4, -4, -4, -10, -2, -2, -9, 0, -4, -6,
     1, -2, -10, -12, -2, 0, -12, 0, -2, -19, -4, -2, -4, -8, -9, 6, 2, 0, 2, -14,
     -7, 6, -4, 2, -1, 2, 2, 0, 8, -8, -6, -4, 0, 14, 10, 0, 8, 8, 0, 12,
     2, -11, -16, 0, 14, -2, 8, 10, -2, -2, -3, -4, -8, 8, 16, 0, 3, 10, -4, -6] := by
  eta_coeff

end WeightTwoCusps
