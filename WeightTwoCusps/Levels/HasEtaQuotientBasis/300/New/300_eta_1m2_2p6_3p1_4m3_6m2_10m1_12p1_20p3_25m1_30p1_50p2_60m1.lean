module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 300

The eta expression is `η(z)^(-2) η(2z)^6 η(3z) η(4z)^(-3) η(6z)^(-2) η(10z)^(-1) η(12z) η(20z)^3 η(25z)^(-1) η(30z) η(50z)^2 η(60z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^6 η(3z) η(4z)^(-3) η(6z)^(-2) η(10z)^(-1) η(12z) η(20z)^3 η(25z)^(-1) η(30z) η(50z)^2 η(60z)^(-1)` at level 300. -/
abbrev cuspForm_300_eta_1m2_2p6_3p1_4m3_6m2_10m1_12p1_20p3_25m1_30p1_50p2_60m1 : gamma0CuspForms 300 :=
  etaQuotientCuspForm 300 sparse![300; 0 => -2, 1 => 6, 2 => 1, 3 => -3, 5 => -2, 9 => -1, 11 => 1, 19 => 3, 24 => -1, 29 => 1, 49 => 2, 59 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_300_eta_1m2_2p6_3p1_4m3_6m2_10m1_12p1_20p3_25m1_30p1_50p2_60m1_first_coeffs :
    first_coeffs 100 cuspForm_300_eta_1m2_2p6_3p1_4m3_6m2_10m1_12p1_20p3_25m1_30p1_50p2_60m1 =
    [0, 0, 0, 0, 1, 2, -1, -3, 0, 1, 0, -2, 0, 3, -2, -1, 1, 0, 0, -3,
     3, 4, -3, -3, -1, 1, 1, 0, 3, 5, 0, -2, -3, 0, 3, -5, 1, 9, 0, -6,
     -3, 3, 0, -6, 0, 5, 0, -3, -3, 0, 0, -4, 6, 9, 2, -6, -5, 0, -3, 1,
     -3, 6, 9, -3, -5, -2, 3, -6, -3, 9, 0, -8, 0, 0, -2, -2, -1, 9, 6, 0,
     -3, -7, 0, -3, 5, 12, 1, 0, -3, -7, 0, 4, -3, 3, 0, 4, -1, -6, 3, -8] := by
  eta_coeff

end WeightTwoCusps
