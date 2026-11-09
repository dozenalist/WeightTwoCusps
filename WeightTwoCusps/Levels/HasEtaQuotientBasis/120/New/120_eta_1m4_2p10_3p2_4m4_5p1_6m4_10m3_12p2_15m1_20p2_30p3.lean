module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 120

The eta expression is `η(z)^(-4) η(2z)^10 η(3z)^2 η(4z)^(-4) η(5z) η(6z)^(-4) η(10z)^(-3) η(12z)^2 η(15z)^(-1) η(20z)^2 η(30z)^3`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^10 η(3z)^2 η(4z)^(-4) η(5z) η(6z)^(-4) η(10z)^(-3) η(12z)^2 η(15z)^(-1) η(20z)^2 η(30z)^3` at level 120. -/
abbrev cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3 : gamma0CuspForms 120 :=
  etaQuotientCuspForm 120 sparse![120; 0 => -4, 1 => 10, 2 => 2, 3 => -4, 4 => 1, 5 => -4, 9 => -3, 11 => 2, 14 => -1, 19 => 2, 29 => 3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3_first_coeffs :
    first_coeffs 100 cuspForm_120_eta_1m4_2p10_3p2_4m4_5p1_6m4_10m3_12p2_15m1_20p2_30p3 =
    [0, 0, 0, 0, 1, 4, 4, -2, -4, -1, -1, 0, 2, 2, -2, -3, 5, 0, -6, 0,
     -2, -1, 2, 4, 1, -6, 2, 0, -6, 0, -3, -4, 0, 0, 2, 0, 1, 2, -4, 2,
     -1, -4, 4, 0, 2, 3, 0, 0, -2, 0, 0, 0, 4, 0, 4, 14, 6, -2, -2, 0,
     -1, 0, 4, 2, -7, -8, -2, 4, 8, 1, 2, 0, -4, 0, 6, 6, -8, -4, 6, -4,
     2, 2, -8, -8, -6, 6, -4, 2, 10, 0, 5, 8, 0, 0, -4, -12, -3, -4, 8, -4] := by
  eta_coeff

end WeightTwoCusps
