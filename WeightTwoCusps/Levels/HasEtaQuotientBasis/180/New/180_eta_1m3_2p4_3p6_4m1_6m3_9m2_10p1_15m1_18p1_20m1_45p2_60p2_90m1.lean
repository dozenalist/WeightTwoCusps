module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 180

The eta expression is `η(z)^(-3) η(2z)^4 η(3z)^6 η(4z)^(-1) η(6z)^(-3) η(9z)^(-2) η(10z) η(15z)^(-1) η(18z) η(20z)^(-1) η(45z)^2 η(60z)^2 η(90z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^4 η(3z)^6 η(4z)^(-1) η(6z)^(-3) η(9z)^(-2) η(10z) η(15z)^(-1) η(18z) η(20z)^(-1) η(45z)^2 η(60z)^2 η(90z)^(-1)` at level 180. -/
abbrev cuspForm_180_eta_1m3_2p4_3p6_4m1_6m3_9m2_10p1_15m1_18p1_20m1_45p2_60p2_90m1 : gamma0CuspForms 180 :=
  etaQuotientCuspForm 180 sparse![180; 0 => -3, 1 => 4, 2 => 6, 3 => -1, 5 => -3, 8 => -2, 9 => 1, 14 => -1, 17 => 1, 19 => -1, 44 => 2, 59 => 2, 89 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_180_eta_1m3_2p4_3p6_4m1_6m3_9m2_10p1_15m1_18p1_20m1_45p2_60p2_90m1_first_coeffs :
    first_coeffs 100 cuspForm_180_eta_1m3_2p4_3p6_4m1_6m3_9m2_10p1_15m1_18p1_20m1_45p2_60p2_90m1 =
    [0, 0, 0, 0, 1, 3, 5, 4, 0, -1, 0, 3, 0, -2, 1, -1, 0, -8, -2, 1,
     1, 6, -4, 2, -7, 0, -1, -4, 2, -2, 2, -8, 4, 2, 5, -7, -3, 0, -4, 2,
     -3, 9, -6, 2, -9, 2, 0, 2, 4, -9, 0, -14, -4, -10, 5, 1, 1, -4, -2, 7,
     3, 8, -2, 2, -5, -1, -14, 4, 6, 8, 1, -18, 10, -2, 9, 0, 5, 10, -4, -4,
     -3, 7, 4, 14, 6, 5, 2, 14, 8, -1, -5, 5, 0, -12, 5, 12, 13, 0, 2, -2] := by
  eta_coeff

end WeightTwoCusps
