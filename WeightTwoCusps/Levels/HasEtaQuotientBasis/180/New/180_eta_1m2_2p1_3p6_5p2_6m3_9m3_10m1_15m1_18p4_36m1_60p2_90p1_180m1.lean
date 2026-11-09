module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 180

The eta expression is `η(z)^(-2) η(2z) η(3z)^6 η(5z)^2 η(6z)^(-3) η(9z)^(-3) η(10z)^(-1) η(15z)^(-1) η(18z)^4 η(36z)^(-1) η(60z)^2 η(90z) η(180z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^6 η(5z)^2 η(6z)^(-3) η(9z)^(-3) η(10z)^(-1) η(15z)^(-1) η(18z)^4 η(36z)^(-1) η(60z)^2 η(90z) η(180z)^(-1)` at level 180. -/
abbrev cuspForm_180_eta_1m2_2p1_3p6_5p2_6m3_9m3_10m1_15m1_18p4_36m1_60p2_90p1_180m1 : gamma0CuspForms 180 :=
  etaQuotientCuspForm 180 sparse![180; 0 => -2, 1 => 1, 2 => 6, 4 => 2, 5 => -3, 8 => -3, 9 => -1, 14 => -1, 17 => 4, 35 => -1, 59 => 2, 89 => 1, 179 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_180_eta_1m2_2p1_3p6_5p2_6m3_9m3_10m1_15m1_18p4_36m1_60p2_90p1_180m1_first_coeffs :
    first_coeffs 100 cuspForm_180_eta_1m2_2p1_3p6_5p2_6m3_9m3_10m1_15m1_18p4_36m1_60p2_90p1_180m1 =
    [0, 1, 2, 4, 2, 2, -2, 0, -4, 0, 1, 6, 4, 0, 2, -2, 1, -8, 0, -3,
     0, -4, -4, 2, -2, 1, -6, 0, -2, -2, 0, 0, 6, -4, -1, -6, -2, 2, 6, 4,
     -2, 0, 4, -2, -6, -2, 0, -4, -4, 0, 2, 4, -2, -4, -2, 1, 2, -8, 4, 10,
     2, -2, -4, -8, -4, 0, 4, 0, 6, 8, -3, -12, 0, 0, -14, 4, 1, 10, 0, 4,
     2, 8, 10, 8, -4, -1, 12, -4, 8, 8, 2, -3, 0, 8, 5, 10, 6, 2, -16, 4] := by
  eta_coeff

end WeightTwoCusps
