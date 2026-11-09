module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 300

The eta expression is `η(z)^(-2) η(2z)^4 η(3z)^2 η(4z)^(-1) η(6z)^(-2) η(10z) η(15z)^(-1) η(20z)^(-1) η(30z) η(50z) η(60z)^2 η(75z) η(150z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z)^2 η(4z)^(-1) η(6z)^(-2) η(10z) η(15z)^(-1) η(20z)^(-1) η(30z) η(50z) η(60z)^2 η(75z) η(150z)^(-1)` at level 300. -/
abbrev cuspForm_300_eta_1m2_2p4_3p2_4m1_6m2_10p1_15m1_20m1_30p1_50p1_60p2_75p1_150m1 : gamma0CuspForms 300 :=
  etaQuotientCuspForm 300 sparse![300; 0 => -2, 1 => 4, 2 => 2, 3 => -1, 5 => -2, 9 => 1, 14 => -1, 19 => -1, 29 => 1, 49 => 1, 59 => 2, 74 => 1, 149 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_300_eta_1m2_2p4_3p2_4m1_6m2_10p1_15m1_20m1_30p1_50p1_60p2_75p1_150m1_first_coeffs :
    first_coeffs 100 cuspForm_300_eta_1m2_2p4_3p2_4m1_6m2_10p1_15m1_20m1_30p1_50p1_60p2_75p1_150m1 =
    [0, 0, 0, 0, 1, 2, 1, 0, -1, 0, 1, 0, 1, -2, -3, -2, -1, 2, 0, 1,
     0, -1, 0, 1, 2, -1, -1, -1, -1, -1, 0, 1, -1, -2, 1, 0, -1, -2, 0, 0,
     -1, 3, 0, 3, -1, 2, 2, -1, 1, -2, 0, -2, 0, 1, 0, -2, 0, 1, 3, -2,
     -1, -3, -3, 3, 1, 2, -2, 0, 1, 2, -2, 1, -1, -2, 0, 1, 3, 0, 3, 3,
     0, 0, 3, 2, -2, -2, 3, 0, 2, 6, 1, -2, 2, 0, 0, -4, 2, 3, -3, 0] := by
  eta_coeff

end WeightTwoCusps
