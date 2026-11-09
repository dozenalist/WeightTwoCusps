module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 300

The eta expression is `η(z)^(-2) η(2z)^5 η(3z)^2 η(4z)^(-2) η(5z) η(6z)^(-3) η(10z)^(-2) η(12z) η(15z)^(-1) η(20z) η(25z) η(30z)^5 η(60z)^(-2) η(75z)^(-1) η(150z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(3z)^2 η(4z)^(-2) η(5z) η(6z)^(-3) η(10z)^(-2) η(12z) η(15z)^(-1) η(20z) η(25z) η(30z)^5 η(60z)^(-2) η(75z)^(-1) η(150z)` at level 300. -/
abbrev cuspForm_300_eta_1m2_2p5_3p2_4m2_5p1_6m3_10m2_12p1_15m1_20p1_25p1_30p5_60m2_75m1_150p1 : gamma0CuspForms 300 :=
  etaQuotientCuspForm 300 sparse![300; 0 => -2, 1 => 5, 2 => 2, 3 => -2, 4 => 1, 5 => -3, 9 => -2, 11 => 1, 14 => -1, 19 => 1, 24 => 1, 29 => 5, 59 => -2, 74 => -1, 149 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_300_eta_1m2_2p5_3p2_4m2_5p1_6m3_10m2_12p1_15m1_20p1_25p1_30p5_60m2_75m1_150p1_first_coeffs :
    first_coeffs 100 cuspForm_300_eta_1m2_2p5_3p2_4m2_5p1_6m3_10m2_12p1_15m1_20p1_25p1_30p5_60m2_75m1_150p1 =
    [0, 0, 0, 0, 0, 1, 2, 0, -2, -2, -1, 0, 0, 2, 0, -3, 0, 2, 2, 0,
     -1, -2, -2, 2, 4, 1, -2, -2, -2, 2, 3, -2, -4, -2, 2, 2, 0, 4, 0, 0,
     5, 2, 4, -6, -4, 3, 0, 2, -2, -2, -3, -2, 4, 4, -4, -4, -2, 0, 6, 2,
     -1, 2, -2, -4, -4, -2, -2, -14, 2, 2, -4, 8, 0, 2, -4, 1, 6, -2, 4, 0,
     -5, 6, 8, -2, -2, -2, -2, -4, 6, 6, -1, 2, 6, 8, 8, 4, -4, 0, -6, 4] := by
  eta_coeff

end WeightTwoCusps
