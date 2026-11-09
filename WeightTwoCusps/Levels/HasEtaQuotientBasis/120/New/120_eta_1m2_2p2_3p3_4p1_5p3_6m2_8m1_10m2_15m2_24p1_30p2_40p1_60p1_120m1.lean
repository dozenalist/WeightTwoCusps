module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 120

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^3 η(4z) η(5z)^3 η(6z)^(-2) η(8z)^(-1) η(10z)^(-2) η(15z)^(-2) η(24z) η(30z)^2 η(40z) η(60z) η(120z)^(-1)`; see
[the local level table](../../TABLE.md#level-120).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^3 η(4z) η(5z)^3 η(6z)^(-2) η(8z)^(-1) η(10z)^(-2) η(15z)^(-2) η(24z) η(30z)^2 η(40z) η(60z) η(120z)^(-1)` at level 120. -/
abbrev cuspForm_120_eta_1m2_2p2_3p3_4p1_5p3_6m2_8m1_10m2_15m2_24p1_30p2_40p1_60p1_120m1 : gamma0CuspForms 120 :=
  etaQuotientCuspForm 120 sparse![120; 0 => -2, 1 => 2, 2 => 3, 3 => 1, 4 => 3, 5 => -2, 7 => -1, 9 => -2, 14 => -2, 23 => 1, 29 => 2, 39 => 1, 59 => 1, 119 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_120_eta_1m2_2p2_3p3_4p1_5p3_6m2_8m1_10m2_15m2_24p1_30p2_40p1_60p1_120m1_first_coeffs :
    first_coeffs 100 cuspForm_120_eta_1m2_2p2_3p3_4p1_5p3_6m2_8m1_10m2_15m2_24p1_30p2_40p1_60p1_120m1 =
    [0, 1, 2, 3, 3, 2, 0, -3, -3, -2, 0, 0, 1, -2, -4, -2, 1, 4, 2, 4,
     -1, -5, -4, 1, -1, -1, 0, -4, -8, -8, -2, -2, 1, 8, 8, -1, 3, -2, 0, -2,
     1, 0, -4, -5, -4, 1, 0, 7, 3, 11, 2, 0, 2, 2, 0, 8, 8, 0, -8, -6,
     -3, -4, 8, 3, 1, -4, 4, 5, 14, 7, 4, -2, -3, -6, -8, 5, -4, -8, 4, 8,
     -3, 9, 4, 3, -8, 2, 0, 0, 4, 6, 0, -6, 0, -10, 8, -4, -5, -6, 2, -8] := by
  eta_coeff

end WeightTwoCusps
