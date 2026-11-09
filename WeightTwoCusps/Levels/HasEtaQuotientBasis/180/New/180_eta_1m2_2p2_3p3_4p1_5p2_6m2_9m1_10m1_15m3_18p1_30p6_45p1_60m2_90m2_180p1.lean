module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 180

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^3 η(4z) η(5z)^2 η(6z)^(-2) η(9z)^(-1) η(10z)^(-1) η(15z)^(-3) η(18z) η(30z)^6 η(45z) η(60z)^(-2) η(90z)^(-2) η(180z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^3 η(4z) η(5z)^2 η(6z)^(-2) η(9z)^(-1) η(10z)^(-1) η(15z)^(-3) η(18z) η(30z)^6 η(45z) η(60z)^(-2) η(90z)^(-2) η(180z)` at level 180. -/
abbrev cuspForm_180_eta_1m2_2p2_3p3_4p1_5p2_6m2_9m1_10m1_15m3_18p1_30p6_45p1_60m2_90m2_180p1 : gamma0CuspForms 180 :=
  etaQuotientCuspForm 180 sparse![180; 0 => -2, 1 => 2, 2 => 3, 3 => 1, 4 => 2, 5 => -2, 8 => -1, 9 => -1, 14 => -3, 17 => 1, 29 => 6, 44 => 1, 59 => -2, 89 => -2, 179 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_180_eta_1m2_2p2_3p3_4p1_5p2_6m2_9m1_10m1_15m3_18p1_30p6_45p1_60m2_90m2_180p1_first_coeffs :
    first_coeffs 100 cuspForm_180_eta_1m2_2p2_3p3_4p1_5p2_6m2_9m1_10m1_15m3_18p1_30p6_45p1_60m2_90m2_180p1 =
    [0, 0, 0, 1, 2, 3, 3, 2, 1, -1, 0, 0, 1, 0, 0, -1, -2, 2, 3, 6,
     2, 4, 0, -1, -1, 0, 0, -3, 0, -5, -3, -4, 6, 0, 0, -8, -7, -12, -9, 2,
     -2, 1, -12, -2, -14, 1, 0, 4, -7, -10, 0, -10, -4, -6, 3, -6, 0, -4, 0, -2,
     7, 4, 0, 0, -2, 3, 0, 14, 7, 8, 0, -4, 7, 12, 18, 1, 8, 3, 6, 0,
     -5, 7, 0, 10, 12, 10, 0, 10, 8, 7, -3, 10, 0, -8, 0, 21, 15, 0, 9, 0] := by
  eta_coeff

end WeightTwoCusps
