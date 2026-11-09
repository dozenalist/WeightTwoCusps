module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 180

The eta expression is `η(z)^(-3) η(2z)^5 η(3z)^3 η(4z)^(-1) η(5z)^2 η(6z)^(-2) η(9z)^(-1) η(10z)^(-1) η(15z)^(-1) η(18z) η(60z)^2 η(90z) η(180z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^5 η(3z)^3 η(4z)^(-1) η(5z)^2 η(6z)^(-2) η(9z)^(-1) η(10z)^(-1) η(15z)^(-1) η(18z) η(60z)^2 η(90z) η(180z)^(-1)` at level 180. -/
abbrev cuspForm_180_eta_1m3_2p5_3p3_4m1_5p2_6m2_9m1_10m1_15m1_18p1_60p2_90p1_180m1 : gamma0CuspForms 180 :=
  etaQuotientCuspForm 180 sparse![180; 0 => -3, 1 => 5, 2 => 3, 3 => -1, 4 => 2, 5 => -2, 8 => -1, 9 => -1, 14 => -1, 17 => 1, 59 => 2, 89 => 1, 179 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_180_eta_1m3_2p5_3p3_4m1_5p2_6m2_9m1_10m1_15m1_18p1_60p2_90p1_180m1_first_coeffs :
    first_coeffs 100 cuspForm_180_eta_1m3_2p5_3p3_4m1_5p2_6m2_9m1_10m1_15m1_18p1_60p2_90p1_180m1 =
    [0, 1, 3, 4, 4, 3, 2, 0, -2, 0, 1, 1, 0, 0, -1, -2, 1, 0, 0, -3,
     0, -4, -8, -1, -2, 1, -5, 0, -2, -3, 0, 0, 5, -4, 1, -9, -2, 2, 1, 4,
     -4, 0, -4, -2, -5, -2, 0, 2, 0, 0, 3, 4, -6, -2, 2, 1, -1, -8, 8, -1,
     2, -2, 2, -8, -6, 4, -4, 0, 1, 8, -5, -2, 4, 0, -9, 4, 3, 3, 0, 4,
     3, 8, 14, 4, 4, -1, 10, -4, 12, 4, -2, -3, 0, 8, 7, 19, 6, 2, -8, 4] := by
  eta_coeff

end WeightTwoCusps
