module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 180

The eta expression is `η(z)^(-3) η(2z)^6 η(3z)^3 η(4z)^(-2) η(5z) η(6z)^(-3) η(10z)^(-2) η(12z) η(15z)^(-3) η(20z) η(30z)^6 η(45z)^2 η(60z)^(-2) η(90z)^(-1)`; see
[the local level table](../../TABLE.md#level-180).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z)^3 η(4z)^(-2) η(5z) η(6z)^(-3) η(10z)^(-2) η(12z) η(15z)^(-3) η(20z) η(30z)^6 η(45z)^2 η(60z)^(-2) η(90z)^(-1)` at level 180. -/
abbrev cuspForm_180_eta_1m3_2p6_3p3_4m2_5p1_6m3_10m2_12p1_15m3_20p1_30p6_45p2_60m2_90m1 : gamma0CuspForms 180 :=
  etaQuotientCuspForm 180 sparse![180; 0 => -3, 1 => 6, 2 => 3, 3 => -2, 4 => 1, 5 => -3, 9 => -2, 11 => 1, 14 => -3, 19 => 1, 29 => 6, 44 => 2, 59 => -2, 89 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_180_eta_1m3_2p6_3p3_4m2_5p1_6m3_10m2_12p1_15m3_20p1_30p6_45p2_60m2_90m1_first_coeffs :
    first_coeffs 100 cuspForm_180_eta_1m3_2p6_3p3_4m2_5p1_6m3_10m2_12p1_15m3_20p1_30p6_45p2_60m2_90m1 =
    [0, 1, 3, 3, 1, -1, -1, 0, -1, 1, 1, -2, -1, 0, 2, -1, 1, 8, 3, 0,
     -1, -2, -2, -2, 5, 1, -8, -3, -2, -2, -3, 0, 5, -4, -2, 2, -1, -4, -2, 2,
     -1, -8, -4, -2, -10, -3, 0, 0, -5, -3, 3, 2, 0, 4, -1, -2, 2, -4, 2, -6,
     1, -2, -4, -2, -3, 2, 8, 6, 8, 6, -2, 12, -3, 6, 0, 3, 0, -6, 6, 4,
     1, 7, 8, -4, 4, 2, 16, -2, 6, 8, 1, 0, 0, 4, 4, 2, -3, 2, -11, 4] := by
  eta_coeff

end WeightTwoCusps
