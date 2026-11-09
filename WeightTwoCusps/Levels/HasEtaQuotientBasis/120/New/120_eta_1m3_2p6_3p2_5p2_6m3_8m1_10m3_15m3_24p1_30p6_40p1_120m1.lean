module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 120

The eta expression is `η(z)^(-3) η(2z)^6 η(3z)^2 η(5z)^2 η(6z)^(-3) η(8z)^(-1) η(10z)^(-3) η(15z)^(-3) η(24z) η(30z)^6 η(40z) η(120z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z)^2 η(5z)^2 η(6z)^(-3) η(8z)^(-1) η(10z)^(-3) η(15z)^(-3) η(24z) η(30z)^6 η(40z) η(120z)^(-1)` at level 120. -/
abbrev cuspForm_120_eta_1m3_2p6_3p2_5p2_6m3_8m1_10m3_15m3_24p1_30p6_40p1_120m1 : gamma0CuspForms 120 :=
  etaQuotientCuspForm 120 sparse![120; 0 => -3, 1 => 6, 2 => 2, 4 => 2, 5 => -3, 7 => -1, 9 => -3, 14 => -3, 23 => 1, 29 => 6, 39 => 1, 119 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_120_eta_1m3_2p6_3p2_5p2_6m3_8m1_10m3_15m3_24p1_30p6_40p1_120m1_first_coeffs :
    first_coeffs 100 cuspForm_120_eta_1m3_2p6_3p2_5p2_6m3_8m1_10m3_15m3_24p1_30p6_40p1_120m1 =
    [0, 0, 1, 3, 3, 2, 0, -5, -6, -3, 0, 2, 2, 2, -2, -1, 5, 4, 1, 0,
     -2, -7, -2, 5, 1, -2, 0, -4, -10, -4, -1, -2, 2, 6, 4, 1, 3, 6, 0, 0,
     -1, -10, -2, -5, -2, 1, 0, -1, 0, 10, 1, 2, 4, 2, 0, 10, 10, 0, -4, -4,
     -3, -6, 4, 1, -7, -6, 2, 1, 16, 11, 2, 2, -6, -4, -4, 5, -8, -8, 2, 0,
     0, 8, 2, -9, -10, 0, 0, 2, 14, 8, 0, 6, 0, -10, 4, -4, -7, -8, 1, -6] := by
  eta_coeff

end WeightTwoCusps
