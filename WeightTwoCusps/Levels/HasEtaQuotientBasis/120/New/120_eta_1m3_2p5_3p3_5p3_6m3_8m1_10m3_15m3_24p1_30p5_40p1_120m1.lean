module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 120

The eta expression is `η(z)^(-3) η(2z)^5 η(3z)^3 η(5z)^3 η(6z)^(-3) η(8z)^(-1) η(10z)^(-3) η(15z)^(-3) η(24z) η(30z)^5 η(40z) η(120z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^5 η(3z)^3 η(5z)^3 η(6z)^(-3) η(8z)^(-1) η(10z)^(-3) η(15z)^(-3) η(24z) η(30z)^5 η(40z) η(120z)^(-1)` at level 120. -/
abbrev cuspForm_120_eta_1m3_2p5_3p3_5p3_6m3_8m1_10m3_15m3_24p1_30p5_40p1_120m1 : gamma0CuspForms 120 :=
  etaQuotientCuspForm 120 sparse![120; 0 => -3, 1 => 5, 2 => 3, 4 => 3, 5 => -3, 7 => -1, 9 => -3, 14 => -3, 23 => 1, 29 => 5, 39 => 1, 119 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_120_eta_1m3_2p5_3p3_5p3_6m3_8m1_10m3_15m3_24p1_30p5_40p1_120m1_first_coeffs :
    first_coeffs 100 cuspForm_120_eta_1m3_2p5_3p3_5p3_6m3_8m1_10m3_15m3_24p1_30p5_40p1_120m1 =
    [0, 1, 3, 4, 4, 2, -2, -6, -7, -3, 0, 2, 3, 0, -4, -1, 6, 6, 5, 2,
     -3, -10, -6, 4, 0, -1, 0, -6, -14, -8, -1, -2, 1, 10, 8, 0, 4, 4, 0, -2,
     0, -8, -8, -8, -2, 0, 2, 4, 1, 15, 3, 4, 6, 2, 0, 10, 14, 2, -8, -6,
     -4, -8, 8, 4, -6, -6, 6, 4, 22, 12, 4, 0, -7, -6, -12, 6, -12, -12, 2, 6,
     -1, 11, 10, -4, -14, 0, -2, -2, 14, 10, -2, 0, 0, -14, 10, -2, -8, -10, -1, -10] := by
  eta_coeff

end WeightTwoCusps
