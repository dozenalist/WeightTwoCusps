module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 180

The eta expression is `η(z)^(-2) η(2z) η(3z)^7 η(6z)^(-3) η(9z)^(-3) η(15z)^(-1) η(18z)^2 η(30z) η(45z)^3 η(90z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^7 η(6z)^(-3) η(9z)^(-3) η(15z)^(-1) η(18z)^2 η(30z) η(45z)^3 η(90z)^(-1)` at level 180. -/
abbrev cuspForm_180_eta_1m2_2p1_3p7_6m3_9m3_15m1_18p2_30p1_45p3_90m1 : gamma0CuspForms 180 :=
  etaQuotientCuspForm 180 sparse![180; 0 => -2, 1 => 1, 2 => 7, 5 => -3, 8 => -3, 14 => -1, 17 => 2, 29 => 1, 44 => 3, 89 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_180_eta_1m2_2p1_3p7_6m3_9m3_15m1_18p2_30p1_45p3_90m1_first_coeffs :
    first_coeffs 100 cuspForm_180_eta_1m2_2p1_3p7_6m3_9m3_15m1_18p2_30p1_45p3_90m1 =
    [0, 0, 0, 1, 2, 4, 1, 0, -4, 1, 0, 0, -1, 0, 8, -1, 0, -8, 1, 2,
     0, 0, -4, 4, 1, 0, -8, -3, 0, 4, -1, 0, 8, 0, 2, -16, -1, -4, 4, 2,
     -2, 12, -4, 0, -16, -1, 0, 0, -1, -2, 0, -2, -4, -8, 1, -2, 8, -4, 4, 8,
     1, 0, -16, 0, -2, 4, 0, 4, 20, 4, -2, -16, 1, 4, 0, 1, 2, 4, 2, 0,
     -4, 5, 4, 8, 4, 2, 16, 2, 4, -12, -1, 2, 0, 0, 2, 28, 1, 0, -20, 0] := by
  eta_coeff

end WeightTwoCusps
