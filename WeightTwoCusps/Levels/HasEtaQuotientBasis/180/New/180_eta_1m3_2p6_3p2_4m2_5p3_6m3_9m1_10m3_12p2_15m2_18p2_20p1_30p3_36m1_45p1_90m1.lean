module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 180

The eta expression is `η(z)^(-3) η(2z)^6 η(3z)^2 η(4z)^(-2) η(5z)^3 η(6z)^(-3) η(9z)^(-1) η(10z)^(-3) η(12z)^2 η(15z)^(-2) η(18z)^2 η(20z) η(30z)^3 η(36z)^(-1) η(45z) η(90z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z)^2 η(4z)^(-2) η(5z)^3 η(6z)^(-3) η(9z)^(-1) η(10z)^(-3) η(12z)^2 η(15z)^(-2) η(18z)^2 η(20z) η(30z)^3 η(36z)^(-1) η(45z) η(90z)^(-1)` at level 180. -/
abbrev cuspForm_180_eta_1m3_2p6_3p2_4m2_5p3_6m3_9m1_10m3_12p2_15m2_18p2_20p1_30p3_36m1_45p1_90m1 : gamma0CuspForms 180 :=
  etaQuotientCuspForm 180 sparse![180; 0 => -3, 1 => 6, 2 => 2, 3 => -2, 4 => 3, 5 => -3, 8 => -1, 9 => -3, 11 => 2, 14 => -2, 17 => 2, 19 => 1, 29 => 3, 35 => -1, 44 => 1, 89 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_180_eta_1m3_2p6_3p2_4m2_5p3_6m3_9m1_10m3_12p2_15m2_18p2_20p1_30p3_36m1_45p1_90m1_first_coeffs :
    first_coeffs 100 cuspForm_180_eta_1m3_2p6_3p2_4m2_5p3_6m3_9m1_10m3_12p2_15m2_18p2_20p1_30p3_36m1_45p1_90m1 =
    [0, 1, 3, 3, 2, 2, 0, -3, -2, 2, 3, 3, 4, 2, -3, -3, 1, -2, 0, 5,
     2, -2, 0, 1, -4, -2, -3, -5, -6, -1, 0, 0, 9, 0, -9, -9, -4, -10, -3, 6,
     -2, -4, 0, 1, -11, -2, 0, -4, -4, 4, 3, -2, 2, 0, 0, -3, -3, -12, 0, 5,
     4, 4, 6, -4, -8, 4, 0, -3, 1, 10, -3, -2, 4, 2, -3, 3, 5, 3, 0, 2,
     1, 12, 18, 2, 0, 2, 6, 2, 20, 8, 0, -3, 0, 4, 9, 19, 12, 8, 0, 0] := by
  eta_coeff

end WeightTwoCusps
