module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 180

The eta expression is `η(z)^(-3) η(2z)^6 η(3z)^3 η(4z)^(-2) η(5z) η(6z)^(-3) η(9z)^(-1) η(10z)^(-2) η(12z) η(15z)^(-1) η(18z)^2 η(20z) η(30z)^3 η(36z)^(-1) η(45z) η(60z)^(-1) η(90z)^(-2) η(180z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z)^3 η(4z)^(-2) η(5z) η(6z)^(-3) η(9z)^(-1) η(10z)^(-2) η(12z) η(15z)^(-1) η(18z)^2 η(20z) η(30z)^3 η(36z)^(-1) η(45z) η(60z)^(-1) η(90z)^(-2) η(180z)^2` at level 180. -/
abbrev cuspForm_180_eta_1m3_2p6_3p3_4m2_5p1_6m3_9m1_10m2_12p1_15m1_18p2_20p1_30p3_36m1_45p1_60m1_90m2_180p2 : gamma0CuspForms 180 :=
  etaQuotientCuspForm 180 sparse![180; 0 => -3, 1 => 6, 2 => 3, 3 => -2, 4 => 1, 5 => -3, 8 => -1, 9 => -2, 11 => 1, 14 => -1, 17 => 2, 19 => 1, 29 => 3, 35 => -1, 44 => 1, 59 => -1, 89 => -2, 179 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_180_eta_1m3_2p6_3p3_4m2_5p1_6m3_9m1_10m2_12p1_15m1_18p2_20p1_30p3_36m1_45p1_60m1_90m2_180p2_first_coeffs :
    first_coeffs 100 cuspForm_180_eta_1m3_2p6_3p3_4m2_5p1_6m3_9m1_10m2_12p1_15m1_18p2_20p1_30p3_36m1_45p1_60m1_90m2_180p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 3, 1, -1, -1, 0, -1, 1, 2,
     1, 2, 1, 1, -2, -1, 1, -2, -1, -1, -1, -2, 2, 2, -2, -2, -4, -3, -2, 2,
     -1, -6, -2, -1, -3, 1, 0, -5, -5, 0, 0, -6, 1, 1, 0, -1, -1, -4, -4, 5,
     4, 4, 2, 0, -4, 1, 2, -1, 0, 4, 1, 0, 3, 0, 3, 0, 4, 2, 2, 0,
     -1, 4, 5, 1, 2, 3, -2, 6, 9, 10, 0, 2, 0, -4, 4, 6, 10, 2, 4, -2] := by
  eta_coeff

end WeightTwoCusps
