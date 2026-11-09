module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 180

The eta expression is `η(z)^(-3) η(2z)^6 η(3z)^3 η(4z)^(-2) η(6z)^(-2) η(9z)^(-1) η(10z) η(15z)^(-1) η(20z)^(-1) η(36z) η(45z)^2 η(60z)^2 η(90z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z)^3 η(4z)^(-2) η(6z)^(-2) η(9z)^(-1) η(10z) η(15z)^(-1) η(20z)^(-1) η(36z) η(45z)^2 η(60z)^2 η(90z)^(-1)` at level 180. -/
abbrev cuspForm_180_eta_1m3_2p6_3p3_4m2_6m2_9m1_10p1_15m1_20m1_36p1_45p2_60p2_90m1 : gamma0CuspForms 180 :=
  etaQuotientCuspForm 180 sparse![180; 0 => -3, 1 => 6, 2 => 3, 3 => -2, 5 => -2, 8 => -1, 9 => 1, 14 => -1, 19 => -1, 35 => 1, 44 => 2, 59 => 2, 89 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_180_eta_1m3_2p6_3p3_4m2_6m2_9m1_10p1_15m1_20m1_36p1_45p2_60p2_90m1_first_coeffs :
    first_coeffs 100 cuspForm_180_eta_1m3_2p6_3p3_4m2_6m2_9m1_10p1_15m1_20m1_36p1_45p2_60p2_90m1 =
    [0, 0, 0, 0, 0, 1, 3, 3, 1, -1, 0, 2, -1, -1, 0, 0, -1, -6, -1, -1,
     0, 4, 1, 3, -3, 0, 0, -2, 1, 1, 1, -6, 0, 0, 1, -4, -1, 3, -3, 0,
     -1, 5, -4, 0, -2, 1, 0, -2, 3, -5, 0, -8, -1, -6, 3, 2, 0, 0, -4, 8,
     1, 6, 0, 2, -2, -1, -8, 0, 1, 4, 2, -12, 5, -4, 6, 0, 5, 5, -2, -2,
     -1, 3, -1, 8, 4, 3, 0, 8, 5, -1, -3, 3, 0, -8, 1, 7, 5, 0, 3, 0] := by
  eta_coeff

end WeightTwoCusps
