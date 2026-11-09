module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 300

The eta expression is `η(z)^(-2) η(2z)^4 η(3z) η(4z)^(-2) η(5z)^3 η(6z)^(-2) η(10z)^(-2) η(12z)^2 η(15z)^(-1) η(20z) η(25z)^(-1) η(30z) η(50z)^2 η(100z)^(-1) η(150z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z) η(4z)^(-2) η(5z)^3 η(6z)^(-2) η(10z)^(-2) η(12z)^2 η(15z)^(-1) η(20z) η(25z)^(-1) η(30z) η(50z)^2 η(100z)^(-1) η(150z)` at level 300. -/
abbrev cuspForm_300_eta_1m2_2p4_3p1_4m2_5p3_6m2_10m2_12p2_15m1_20p1_25m1_30p1_50p2_100m1_150p1 : gamma0CuspForms 300 :=
  etaQuotientCuspForm 300 sparse![300; 0 => -2, 1 => 4, 2 => 1, 3 => -2, 4 => 3, 5 => -2, 9 => -2, 11 => 2, 14 => -1, 19 => 1, 24 => -1, 29 => 1, 49 => 2, 99 => -1, 149 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_300_eta_1m2_2p4_3p1_4m2_5p3_6m2_10m2_12p2_15m1_20p1_25m1_30p1_50p2_100m1_150p1_first_coeffs :
    first_coeffs 100 cuspForm_300_eta_1m2_2p4_3p1_4m2_5p3_6m2_10m2_12p2_15m1_20p1_25m1_30p1_50p2_100m1_150p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 1, 2, 0, -2, 1, 3, 1, 0, 1, 1,
     -3, -2, 2, 2, 0, 0, 1, 1, 0, -3, 1, 0, -1, 1, 0, 0, -1, -2, -3, 2,
     3, 1, -2, 1, 1, -6, -1, 2, -1, -1, -1, 0, -2, -3, -2, 0, 0, -2, -2, -2,
     1, -5, 0, 0, -2, 0, -2, -1, -3, -3, -4, 1, 3, 2, -2, -3, -3, -5, -1, 4,
     1, 1, -2, 0, -1, 0, 1, -2, 0, 0, 1, 0, 5, -1, -1, 0, 1, 2, 4, 1] := by
  eta_coeff

end WeightTwoCusps
