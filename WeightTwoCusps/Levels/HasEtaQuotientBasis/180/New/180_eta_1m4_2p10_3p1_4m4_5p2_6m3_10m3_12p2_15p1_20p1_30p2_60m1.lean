module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 180

The eta expression is `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(5z)^2 η(6z)^(-3) η(10z)^(-3) η(12z)^2 η(15z) η(20z) η(30z)^2 η(60z)^(-1)`; see
[the local level table](../../TABLE.md#level-180).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(5z)^2 η(6z)^(-3) η(10z)^(-3) η(12z)^2 η(15z) η(20z) η(30z)^2 η(60z)^(-1)` at level 180. -/
abbrev cuspForm_180_eta_1m4_2p10_3p1_4m4_5p2_6m3_10m3_12p2_15p1_20p1_30p2_60m1 : gamma0CuspForms 180 :=
  etaQuotientCuspForm 180 sparse![180; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 4 => 2, 5 => -3, 9 => -3, 11 => 2, 14 => 1, 19 => 1, 29 => 2, 59 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_180_eta_1m4_2p10_3p1_4m4_5p2_6m3_10m3_12p2_15p1_20p1_30p2_60m1_first_coeffs :
    first_coeffs 100 cuspForm_180_eta_1m4_2p10_3p1_4m4_5p2_6m3_10m3_12p2_15p1_20p1_30p2_60m1 =
    [0, 1, 4, 4, -1, 0, 2, -6, -4, 6, 1, -2, 4, 0, -6, -2, -3, -12, -8, 6,
     2, -4, 14, 8, -14, -5, -2, -12, -6, 12, 8, 0, 8, -4, -16, -6, 2, -4, 4, 4,
     5, 18, 12, 16, -2, -8, 0, -4, 12, 15, 4, 4, 8, -8, 2, 4, -6, -8, -2, 14,
     -2, 10, 12, 4, 7, -2, -20, -24, -8, 8, 0, -20, 8, -18, -22, 4, 2, 0, -16, -8,
     6, 14, -8, 4, -12, -10, 4, -4, -2, -26, -2, -18, 0, 8, -10, 4, 10, 14, -4, 4] := by
  eta_coeff

end WeightTwoCusps
