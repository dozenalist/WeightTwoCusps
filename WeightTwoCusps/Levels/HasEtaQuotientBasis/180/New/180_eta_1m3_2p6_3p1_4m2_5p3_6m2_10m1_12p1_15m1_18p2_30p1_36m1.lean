module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 180

The eta expression is `η(z)^(-3) η(2z)^6 η(3z) η(4z)^(-2) η(5z)^3 η(6z)^(-2) η(10z)^(-1) η(12z) η(15z)^(-1) η(18z)^2 η(30z) η(36z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z) η(4z)^(-2) η(5z)^3 η(6z)^(-2) η(10z)^(-1) η(12z) η(15z)^(-1) η(18z)^2 η(30z) η(36z)^(-1)` at level 180. -/
abbrev cuspForm_180_eta_1m3_2p6_3p1_4m2_5p3_6m2_10m1_12p1_15m1_18p2_30p1_36m1 : gamma0CuspForms 180 :=
  etaQuotientCuspForm 180 sparse![180; 0 => -3, 1 => 6, 2 => 1, 3 => -2, 4 => 3, 5 => -2, 9 => -1, 11 => 1, 14 => -1, 17 => 2, 29 => 1, 35 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_180_eta_1m3_2p6_3p1_4m2_5p3_6m2_10m1_12p1_15m1_18p2_30p1_36m1_first_coeffs :
    first_coeffs 100 cuspForm_180_eta_1m3_2p6_3p1_4m2_5p3_6m2_10m1_12p1_15m1_18p2_30p1_36m1 =
    [0, 1, 3, 3, 3, 5, 3, 0, 3, 5, 3, 4, 3, 0, 0, -1, 3, 6, 3, 0,
     -3, -6, -6, -4, -3, 1, -6, -7, -6, -12, -3, 0, -3, -4, -6, -14, -9, -4, -6, 2,
     -3, -12, -12, -2, 0, -7, 0, 2, -9, -3, 3, 10, 0, -2, 3, -2, 0, -4, 6, -4,
     9, -2, 0, 2, -9, 8, 0, 6, 0, 2, -6, 4, 9, 6, 6, 3, 0, 6, 6, 4,
     3, 7, 24, 10, 12, 2, 12, -10, 18, 28, -3, 0, 0, 12, 12, 38, 21, 2, -3, 4] := by
  eta_coeff

end WeightTwoCusps
