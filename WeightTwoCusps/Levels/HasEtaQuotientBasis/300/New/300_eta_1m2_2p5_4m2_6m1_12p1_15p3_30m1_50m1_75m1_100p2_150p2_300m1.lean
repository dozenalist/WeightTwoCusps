module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 300

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(6z)^(-1) η(12z) η(15z)^3 η(30z)^(-1) η(50z)^(-1) η(75z)^(-1) η(100z)^2 η(150z)^2 η(300z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(6z)^(-1) η(12z) η(15z)^3 η(30z)^(-1) η(50z)^(-1) η(75z)^(-1) η(100z)^2 η(150z)^2 η(300z)^(-1)` at level 300. -/
abbrev cuspForm_300_eta_1m2_2p5_4m2_6m1_12p1_15p3_30m1_50m1_75m1_100p2_150p2_300m1 : gamma0CuspForms 300 :=
  etaQuotientCuspForm 300 sparse![300; 0 => -2, 1 => 5, 3 => -2, 5 => -1, 11 => 1, 14 => 3, 29 => -1, 49 => -1, 74 => -1, 99 => 2, 149 => 2, 299 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_300_eta_1m2_2p5_4m2_6m1_12p1_15p3_30m1_50m1_75m1_100p2_150p2_300m1_first_coeffs :
    first_coeffs 100 cuspForm_300_eta_1m2_2p5_4m2_6m1_12p1_15p3_30m1_50m1_75m1_100p2_150p2_300m1 =
    [0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 1, 2, 0, 2, 2, 0, 1, 2, 0, -1,
     -2, 0, 2, -2, 0, -1, 0, 0, -4, 0, 0, 1, 0, 0, -2, -2, 0, -2, 0, 0,
     1, -6, 0, 2, -4, 0, -4, -2, 0, 3, 0, 0, -2, -4, 1, -2, 0, 0, 2, -2,
     1, -1, -6, 2, 1, 2, 1, 2, 2, -1, -2, 4, 2, -4, -2, -1, 4, -2, -4, 0,
     2, 1, 0, 2, -2, 2, 2, -2, 2, 6, 1, -3, 6, 2, -4, -4, -4, 0, -2, 3] := by
  eta_coeff

end WeightTwoCusps
