module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 120

The eta expression is `η(z)^(-2) η(2z)^3 η(3z) η(4z) η(5z)^2 η(8z)^(-1) η(10z)^(-2) η(15z)^(-1) η(30z)^3 η(40z) η(60z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z) η(4z) η(5z)^2 η(8z)^(-1) η(10z)^(-2) η(15z)^(-1) η(30z)^3 η(40z) η(60z)^(-1)` at level 120. -/
abbrev cuspForm_120_eta_1m2_2p3_3p1_4p1_5p2_8m1_10m2_15m1_30p3_40p1_60m1 : gamma0CuspForms 120 :=
  etaQuotientCuspForm 120 sparse![120; 0 => -2, 1 => 3, 2 => 1, 3 => 1, 4 => 2, 7 => -1, 9 => -2, 14 => -1, 29 => 3, 39 => 1, 59 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_120_eta_1m2_2p3_3p1_4p1_5p2_8m1_10m2_15m1_30p3_40p1_60m1_first_coeffs :
    first_coeffs 100 cuspForm_120_eta_1m2_2p3_3p1_4p1_5p2_8m1_10m2_15m1_30p3_40p1_60m1 =
    [0, 0, 1, 2, 2, 3, 2, 0, -1, -2, -2, -2, 1, 2, 0, -1, 0, -4, -5, 2,
     -1, 0, 2, 2, -2, -2, 4, -2, -6, -2, -1, -10, -1, 2, -4, -2, 2, -2, -8, 2,
     2, -2, 0, 6, -2, 3, 6, 6, 3, -2, 1, -8, 2, 8, 8, 6, 6, -2, 4, 2,
     -2, 10, 0, 2, 4, 0, -2, 6, 10, 6, 0, 4, -1, -8, 8, 4, -4, -4, 2, -6,
     -3, 6, -2, -14, -6, 2, -14, 6, -2, 0, 4, 4, 0, -14, -10, -10, -2, -4, 5, -6] := by
  eta_coeff

end WeightTwoCusps
