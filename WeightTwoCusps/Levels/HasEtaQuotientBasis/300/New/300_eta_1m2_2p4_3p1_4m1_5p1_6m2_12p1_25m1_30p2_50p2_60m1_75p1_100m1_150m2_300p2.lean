module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 300

The eta expression is `η(z)^(-2) η(2z)^4 η(3z) η(4z)^(-1) η(5z) η(6z)^(-2) η(12z) η(25z)^(-1) η(30z)^2 η(50z)^2 η(60z)^(-1) η(75z) η(100z)^(-1) η(150z)^(-2) η(300z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z) η(4z)^(-1) η(5z) η(6z)^(-2) η(12z) η(25z)^(-1) η(30z)^2 η(50z)^2 η(60z)^(-1) η(75z) η(100z)^(-1) η(150z)^(-2) η(300z)^2` at level 300. -/
abbrev cuspForm_300_eta_1m2_2p4_3p1_4m1_5p1_6m2_12p1_25m1_30p2_50p2_60m1_75p1_100m1_150m2_300p2 : gamma0CuspForms 300 :=
  etaQuotientCuspForm 300 sparse![300; 0 => -2, 1 => 4, 2 => 1, 3 => -1, 4 => 1, 5 => -2, 11 => 1, 24 => -1, 29 => 2, 49 => 2, 59 => -1, 74 => 1, 99 => -1, 149 => -2, 299 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_300_eta_1m2_2p4_3p1_4m1_5p1_6m2_12p1_25m1_30p2_50p2_60m1_75p1_100m1_150m2_300p2_first_coeffs :
    first_coeffs 100 cuspForm_300_eta_1m2_2p4_3p1_4m1_5p1_6m2_12p1_25m1_30p2_50p2_60m1_75p1_100m1_150m2_300p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 1, 1,
     0, 1, 2, 2, 1, 0, -1, 0, 1, 2, 2, -2, -1, 0, 2, 2, 0, 0, -2, -1,
     2, 6, 1, -1, -1, -4, -2, 2, 1, -5, -2, -2, -2, -1, 0, 0, -3, -2, 1, 1,
     -2, 0, -2, -3, -4, 0, 3, -4, -2, 0, -4, -7, 1, 0, -6, -1, 2, -3, -5, 3,
     -4, -5, -3, 1, 1, -4, 1, -1, -4, -5, 0, 1, -1, 1, 4, 0, -3, 3, 2, -2] := by
  eta_coeff

end WeightTwoCusps
