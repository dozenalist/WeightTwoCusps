module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 300

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^2 η(4z)^(-1) η(5z)^3 η(6z)^(-2) η(10z)^(-2) η(12z) η(15z)^(-2) η(20z) η(30z)^3 η(60z)^(-1) η(75z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^2 η(4z)^(-1) η(5z)^3 η(6z)^(-2) η(10z)^(-2) η(12z) η(15z)^(-2) η(20z) η(30z)^3 η(60z)^(-1) η(75z)` at level 300. -/
abbrev cuspForm_300_eta_1m2_2p3_3p2_4m1_5p3_6m2_10m2_12p1_15m2_20p1_30p3_60m1_75p1 : gamma0CuspForms 300 :=
  etaQuotientCuspForm 300 sparse![300; 0 => -2, 1 => 3, 2 => 2, 3 => -1, 4 => 3, 5 => -2, 9 => -2, 11 => 1, 14 => -2, 19 => 1, 29 => 3, 59 => -1, 74 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_300_eta_1m2_2p3_3p2_4m1_5p3_6m2_10m2_12p1_15m2_20p1_30p3_60m1_75p1_first_coeffs :
    first_coeffs 100 cuspForm_300_eta_1m2_2p3_3p2_4m1_5p3_6m2_10m2_12p1_15m2_20p1_30p3_60m1_75p1 =
    [0, 0, 0, 0, 1, 2, 2, 2, 2, 1, -1, 0, 2, 2, 0, 1, 1, -2, 0, 3,
     4, 1, 2, 2, 0, -1, 2, 2, -2, 0, 0, -1, -4, -2, 0, 0, -2, 2, 0, -3,
     -3, 0, 0, -4, -2, -4, -4, -6, 0, -3, 0, -1, 0, 0, -1, -2, -4, 2, 2, -2,
     -3, 1, -6, 0, 1, 2, -5, -4, -2, 0, 2, 4, 2, -4, 2, -2, 2, -2, -4, -4,
     -4, -3, 0, -2, -2, -2, 0, -2, -6, 0, -1, -1, 2, 2, -8, -4, 0, 0, -2, 1] := by
  eta_coeff

end WeightTwoCusps
