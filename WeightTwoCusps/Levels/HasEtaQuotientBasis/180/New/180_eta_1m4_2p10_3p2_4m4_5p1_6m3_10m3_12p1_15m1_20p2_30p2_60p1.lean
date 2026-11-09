module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 180

The eta expression is `η(z)^(-4) η(2z)^10 η(3z)^2 η(4z)^(-4) η(5z) η(6z)^(-3) η(10z)^(-3) η(12z) η(15z)^(-1) η(20z)^2 η(30z)^2 η(60z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^10 η(3z)^2 η(4z)^(-4) η(5z) η(6z)^(-3) η(10z)^(-3) η(12z) η(15z)^(-1) η(20z)^2 η(30z)^2 η(60z)` at level 180. -/
abbrev cuspForm_180_eta_1m4_2p10_3p2_4m4_5p1_6m3_10m3_12p1_15m1_20p2_30p2_60p1 : gamma0CuspForms 180 :=
  etaQuotientCuspForm 180 sparse![180; 0 => -4, 1 => 10, 2 => 2, 3 => -4, 4 => 1, 5 => -3, 9 => -3, 11 => 1, 14 => -1, 19 => 2, 29 => 2, 59 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_180_eta_1m4_2p10_3p2_4m4_5p1_6m3_10m3_12p1_15m1_20p2_30p2_60p1_first_coeffs :
    first_coeffs 100 cuspForm_180_eta_1m4_2p10_3p2_4m4_5p1_6m3_10m3_12p1_15m1_20p2_30p2_60p1 =
    [0, 0, 0, 0, 0, 1, 4, 4, -2, -4, -1, -2, -4, -2, 4, 2, -2, 6, 0, -8,
     -2, 0, 2, -4, 0, 3, -4, 8, 2, -6, 0, -2, -2, -4, 2, 2, 0, 12, 8, -4,
     0, 0, -8, -4, 4, 2, 0, 8, 4, -6, 0, 4, -2, -2, 4, 4, 4, 8, -2, -10,
     0, -4, -8, -4, 2, 0, -8, 4, 4, -4, 2, 4, 4, -2, -12, 0, 4, 0, 0, 2,
     2, -8, -8, 4, 8, -1, 8, -4, -2, 4, -4, 2, 0, 0, -4, 0, 0, -6, -16, 4] := by
  eta_coeff

end WeightTwoCusps
