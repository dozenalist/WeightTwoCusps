module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 300

The eta expression is `η(z)^(-3) η(2z)^6 η(3z) η(4z)^(-2) η(5z)^3 η(6z)^(-2) η(10z)^(-1) η(12z) η(15z)^(-1) η(30z) η(50z)^2 η(100z)^(-1)`; see
[the local level table](../../TABLE.md#level-300).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z) η(4z)^(-2) η(5z)^3 η(6z)^(-2) η(10z)^(-1) η(12z) η(15z)^(-1) η(30z) η(50z)^2 η(100z)^(-1)` at level 300. -/
abbrev cuspForm_300_eta_1m3_2p6_3p1_4m2_5p3_6m2_10m1_12p1_15m1_30p1_50p2_100m1 : gamma0CuspForms 300 :=
  etaQuotientCuspForm 300 sparse![300; 0 => -3, 1 => 6, 2 => 1, 3 => -2, 4 => 3, 5 => -2, 9 => -1, 11 => 1, 14 => -1, 29 => 1, 49 => 2, 99 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_300_eta_1m3_2p6_3p1_4m2_5p3_6m2_10m1_12p1_15m1_30p1_50p2_100m1_first_coeffs :
    first_coeffs 100 cuspForm_300_eta_1m3_2p6_3p1_4m2_5p3_6m2_10m1_12p1_15m1_30p1_50p2_100m1 =
    [0, 1, 3, 3, 3, 5, 3, 0, 3, 5, 3, 4, 3, 0, 0, -1, 3, 6, 3, 2,
     3, 0, 0, 6, 3, 1, 0, 3, 0, -4, 3, 0, -3, -6, 0, -2, -3, 0, 0, 2,
     -3, 0, -6, 0, 0, -1, 0, -6, -3, -3, -3, -4, -6, -12, -9, -12, -6, 0, -6, -14,
     -9, -10, -6, 0, -9, -2, -12, -12, -12, -6, -12, -8, 3, -12, -6, -5, -6, -18, -6, 8,
     -9, -3, 6, 6, -6, 6, 6, -12, 0, -4, 3, -4, 6, 6, 0, 4, 3, 12, -3, -2] := by
  eta_coeff

end WeightTwoCusps
