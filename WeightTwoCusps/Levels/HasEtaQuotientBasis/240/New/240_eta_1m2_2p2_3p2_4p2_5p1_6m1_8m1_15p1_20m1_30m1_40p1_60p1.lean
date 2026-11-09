module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^2 η(4z)^2 η(5z) η(6z)^(-1) η(8z)^(-1) η(15z) η(20z)^(-1) η(30z)^(-1) η(40z) η(60z)`; see
[the local level table](../../TABLE.md#level-240).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^2 η(4z)^2 η(5z) η(6z)^(-1) η(8z)^(-1) η(15z) η(20z)^(-1) η(30z)^(-1) η(40z) η(60z)` at level 240. -/
abbrev cuspForm_240_eta_1m2_2p2_3p2_4p2_5p1_6m1_8m1_15p1_20m1_30m1_40p1_60p1 : gamma0CuspForms 240 :=
  etaQuotientCuspForm 240 sparse![240; 0 => -2, 1 => 2, 2 => 2, 3 => 2, 4 => 1, 5 => -1, 7 => -1, 14 => 1, 19 => -1, 29 => -1, 39 => 1, 59 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m2_2p2_3p2_4p2_5p1_6m1_8m1_15p1_20m1_30m1_40p1_60p1_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m2_2p2_3p2_4p2_5p1_6m1_8m1_15p1_20m1_30m1_40p1_60p1 =
    [0, 0, 0, 1, 2, 3, 4, 3, 3, 2, 3, 4, 3, 4, 2, 1, 0, 2, 0, 0,
     -1, -4, -2, -5, 2, -2, -2, 2, -2, -2, -1, 2, -1, 2, -2, -3, -6, -4, 4, -4,
     -2, -2, -10, -7, -2, 1, 0, -3, -5, -6, -4, -4, 2, -8, -8, -4, -10, -4, -6, 2,
     -4, -2, -4, -1, -4, -6, 14, -9, 2, -2, -2, 2, 3, 8, -6, -1, -4, 0, -10, 8,
     5, -2, 8, 1, 2, 0, -4, 0, -2, 4, 3, -10, 4, 4, 4, 4, 6, 0, 8, 4] := by
  eta_coeff

end WeightTwoCusps
