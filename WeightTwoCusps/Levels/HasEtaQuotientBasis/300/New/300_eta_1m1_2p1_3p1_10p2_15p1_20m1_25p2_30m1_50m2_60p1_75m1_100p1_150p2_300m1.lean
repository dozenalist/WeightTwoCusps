module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 300

The eta expression is `η(z)^(-1) η(2z) η(3z) η(10z)^2 η(15z) η(20z)^(-1) η(25z)^2 η(30z)^(-1) η(50z)^(-2) η(60z) η(75z)^(-1) η(100z) η(150z)^2 η(300z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z) η(10z)^2 η(15z) η(20z)^(-1) η(25z)^2 η(30z)^(-1) η(50z)^(-2) η(60z) η(75z)^(-1) η(100z) η(150z)^2 η(300z)^(-1)` at level 300. -/
abbrev cuspForm_300_eta_1m1_2p1_3p1_10p2_15p1_20m1_25p2_30m1_50m2_60p1_75m1_100p1_150p2_300m1 : gamma0CuspForms 300 :=
  etaQuotientCuspForm 300 sparse![300; 0 => -1, 1 => 1, 2 => 1, 9 => 2, 14 => 1, 19 => -1, 24 => 2, 29 => -1, 49 => -2, 59 => 1, 74 => -1, 99 => 1, 149 => 2, 299 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_300_eta_1m1_2p1_3p1_10p2_15p1_20m1_25p2_30m1_50m2_60p1_75m1_100p1_150p2_300m1_first_coeffs :
    first_coeffs 100 cuspForm_300_eta_1m1_2p1_3p1_10p2_15p1_20m1_25p2_30m1_50m2_60p1_75m1_100p1_150p2_300m1 =
    [0, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 2, 0, 2, 0, 1,
     1, -1, 1, 1, 1, 0, -2, -1, 0, -1, -1, -2, -3, -4, -3, -4, 0, -2, -3, -3,
     -4, 2, -3, 1, -1, -1, 1, -3, 0, -3, 1, 0, 0, -4, -3, -2, -1, 4, 0, 1,
     -2, -3, 1, 3, 1, 0, -5, -2, -4, -1, -2, 0, 1, -5, 2, -3, 0, -5, 2, 3,
     1, -4, -5, 2, -4, 8, 0, -3, -3, -2, 2, 1, 3, 4, 1, 0, 0, 3, 4, 0] := by
  eta_coeff

end WeightTwoCusps
