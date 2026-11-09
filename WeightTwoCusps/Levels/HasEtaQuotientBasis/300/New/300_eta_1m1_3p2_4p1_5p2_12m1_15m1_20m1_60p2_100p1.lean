module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 300

The eta expression is `η(z)^(-1) η(3z)^2 η(4z) η(5z)^2 η(12z)^(-1) η(15z)^(-1) η(20z)^(-1) η(60z)^2 η(100z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^2 η(4z) η(5z)^2 η(12z)^(-1) η(15z)^(-1) η(20z)^(-1) η(60z)^2 η(100z)` at level 300. -/
abbrev cuspForm_300_eta_1m1_3p2_4p1_5p2_12m1_15m1_20m1_60p2_100p1 : gamma0CuspForms 300 :=
  etaQuotientCuspForm 300 sparse![300; 0 => -1, 2 => 2, 3 => 1, 4 => 2, 11 => -1, 14 => -1, 19 => -1, 59 => 2, 99 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_300_eta_1m1_3p2_4p1_5p2_12m1_15m1_20m1_60p2_100p1_first_coeffs :
    first_coeffs 100 cuspForm_300_eta_1m1_3p2_4p1_5p2_12m1_15m1_20m1_60p2_100p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 1, 2, 0, 0, -1, 0, -1, -2, -1,
     -3, -1, -2, 2, 0, 1, 0, 0, -3, -1, 0, 0, -1, 0, 0, -1, 0, 1, 4, -2,
     1, -4, -2, -2, 0, 3, 0, 2, -1, 3, 0, 3, 3, -1, 0, -2, 0, 1, 0, 2,
     1, 0, -2, -2, 0, -2, 0, -2, 2, -1, -4, 5, -1, 1, 0, 0, 0, -2, 6, -1,
     3, -1, 6, 0, 0, 4, 0, -2, 2, 1, 2, 1, 2, 1, 0, 4, 0, 2, -6, 1] := by
  eta_coeff

end WeightTwoCusps
