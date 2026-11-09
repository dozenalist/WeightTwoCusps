module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 180

The eta expression is `η(z)^(-3) η(2z)^4 η(3z)^4 η(4z)^(-1) η(5z)^3 η(6z)^(-2) η(9z)^(-1) η(10z)^(-1) η(15z)^(-1) η(30z) η(36z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^4 η(3z)^4 η(4z)^(-1) η(5z)^3 η(6z)^(-2) η(9z)^(-1) η(10z)^(-1) η(15z)^(-1) η(30z) η(36z)` at level 180. -/
abbrev cuspForm_180_eta_1m3_2p4_3p4_4m1_5p3_6m2_9m1_10m1_15m1_30p1_36p1 : gamma0CuspForms 180 :=
  etaQuotientCuspForm 180 sparse![180; 0 => -3, 1 => 4, 2 => 4, 3 => -1, 4 => 3, 5 => -2, 8 => -1, 9 => -1, 14 => -1, 29 => 1, 35 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_180_eta_1m3_2p4_3p4_4m1_5p3_6m2_9m1_10m1_15m1_30p1_36p1_first_coeffs :
    first_coeffs 100 cuspForm_180_eta_1m3_2p4_3p4_4m1_5p3_6m2_9m1_10m1_15m1_30p1_36p1 =
    [0, 0, 1, 3, 5, 6, 6, 6, 3, 0, 0, 3, 3, 0, 1, 0, -2, -6, 1, 3,
     0, 0, -2, 0, -8, 0, -3, -3, -4, 0, -1, -12, 3, -6, -5, -21, -10, -6, -12, 0,
     -1, 3, -14, -6, -13, -3, 0, 0, -5, -15, 1, 0, -6, 0, 6, -3, 1, 0, 14, 3,
     10, 12, -2, 0, 3, 9, -10, 12, 8, 6, -7, -6, 15, 6, 23, 3, 3, 6, 2, 0,
     -4, 6, 2, 0, 14, 15, 6, 0, 2, -3, -6, 15, 0, 0, -5, 36, 28, 0, 7, 6] := by
  eta_coeff

end WeightTwoCusps
