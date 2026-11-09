module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 180

The eta expression is `η(z)^(-4) η(2z)^8 η(3z)^3 η(4z)^(-3) η(5z)^2 η(6z)^(-3) η(10z)^(-1) η(12z) η(15z)^(-1) η(30z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^8 η(3z)^3 η(4z)^(-3) η(5z)^2 η(6z)^(-3) η(10z)^(-1) η(12z) η(15z)^(-1) η(30z)^2` at level 180. -/
abbrev cuspForm_180_eta_1m4_2p8_3p3_4m3_5p2_6m3_10m1_12p1_15m1_30p2 : gamma0CuspForms 180 :=
  etaQuotientCuspForm 180 sparse![180; 0 => -4, 1 => 8, 2 => 3, 3 => -3, 4 => 2, 5 => -3, 9 => -1, 11 => 1, 14 => -1, 29 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_180_eta_1m4_2p8_3p3_4m3_5p2_6m3_10m1_12p1_15m1_30p2_first_coeffs :
    first_coeffs 100 cuspForm_180_eta_1m4_2p8_3p3_4m3_5p2_6m3_10m1_12p1_15m1_30p2 =
    [0, 0, 1, 4, 6, 5, 4, 4, 3, 0, 2, 8, 4, -4, -4, 0, -2, -4, 4, 8,
     -1, -8, 0, 0, -4, 0, 2, 4, -8, -8, -4, -8, -5, -8, -12, -16, -12, -12, -4, 0,
     -2, -8, -16, 8, 8, -4, 0, -4, -12, -16, 1, 16, -4, -4, 4, -4, -4, 0, 12, 8,
     12, 8, 8, -8, -2, 6, 0, 16, -10, 0, -8, -8, 12, 8, 2, 4, 8, 12, 8, -8,
     3, 0, 12, 12, 16, 8, -4, -16, 16, 24, -4, 8, 0, 16, 0, 36, 28, 0, 9, 8] := by
  eta_coeff

end WeightTwoCusps
