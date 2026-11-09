module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 180

The eta expression is `η(z)^(-3) η(2z)^2 η(3z)^7 η(5z)^3 η(6z)^(-3) η(9z)^(-2) η(10z)^(-1) η(15z)^(-1) η(18z) η(30z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^2 η(3z)^7 η(5z)^3 η(6z)^(-3) η(9z)^(-2) η(10z)^(-1) η(15z)^(-1) η(18z) η(30z)` at level 180. -/
abbrev cuspForm_180_eta_1m3_2p2_3p7_5p3_6m3_9m2_10m1_15m1_18p1_30p1 : gamma0CuspForms 180 :=
  etaQuotientCuspForm 180 sparse![180; 0 => -3, 1 => 2, 2 => 7, 4 => 3, 5 => -3, 8 => -2, 9 => -1, 14 => -1, 17 => 1, 29 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_180_eta_1m3_2p2_3p7_5p3_6m3_9m2_10m1_15m1_18p1_30p1_first_coeffs :
    first_coeffs 100 cuspForm_180_eta_1m3_2p2_3p7_5p3_6m3_9m2_10m1_15m1_18p1_30p1 =
    [0, 1, 3, 7, 9, 11, 9, 8, 3, 1, 3, 6, 9, 2, 6, -1, 3, -6, 3, 2,
     -3, -4, -12, 0, -15, 1, -12, -5, -12, -6, -3, -16, 3, -12, -12, -38, -21, -10, -12, 2,
     -3, 0, -24, -16, -18, -7, 0, 0, -15, -21, 3, 6, -6, -6, 9, -6, 6, -4, 30, 6,
     21, 14, -12, -4, -3, 16, -12, 20, 18, 12, -18, -12, 27, 14, 24, 7, -6, 12, 6, 8,
     -3, 13, 30, 12, 24, 24, 24, -6, 12, 12, -9, 22, 0, 8, 6, 76, 57, 2, -9, 12] := by
  eta_coeff

end WeightTwoCusps
