module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-2) η(2z)^3 η(3z) η(4z)^(-1) η(5z)^2 η(8z)^2 η(10z)^(-1) η(15z) η(16z)^(-1) η(24z)^(-1) η(30z)^(-1) η(48z) η(60z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z) η(4z)^(-1) η(5z)^2 η(8z)^2 η(10z)^(-1) η(15z) η(16z)^(-1) η(24z)^(-1) η(30z)^(-1) η(48z) η(60z)` at level 240. -/
abbrev cuspForm_240_eta_1m2_2p3_3p1_4m1_5p2_8p2_10m1_15p1_16m1_24m1_30m1_48p1_60p1 : gamma0CuspForms 240 :=
  etaQuotientCuspForm 240 sparse![240; 0 => -2, 1 => 3, 2 => 1, 3 => -1, 4 => 2, 7 => 2, 9 => -1, 14 => 1, 15 => -1, 23 => -1, 29 => -1, 47 => 1, 59 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m2_2p3_3p1_4m1_5p2_8p2_10m1_15p1_16m1_24m1_30m1_48p1_60p1_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m2_2p3_3p1_4m1_5p2_8p2_10m1_15p1_16m1_24m1_30m1_48p1_60p1 =
    [0, 0, 0, 1, 2, 2, 3, 4, 4, 3, 4, 4, 2, 2, 2, 2, 0, 4, 2, -2,
     0, -1, -4, -8, 0, -4, -4, -1, 0, 0, -3, 6, -4, -2, 0, -2, -6, -2, 8, -4,
     0, -2, -2, -2, -4, 1, -6, -4, -4, -6, -4, -4, 0, -10, -7, -6, -8, -4, -12, 4,
     -4, -6, -4, -4, 0, -6, 8, -10, 0, -3, -2, 4, 4, 12, -12, 1, 0, 4, -6, 2,
     4, -4, 8, 2, 4, 0, 6, -2, -8, 4, 2, -8, 4, 10, 14, 4, 8, 4, 8, 8] := by
  eta_coeff

end WeightTwoCusps
