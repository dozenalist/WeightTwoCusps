module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 180

The eta expression is `η(z)^(-4) η(2z)^9 η(3z)^2 η(4z)^(-3) η(5z) η(6z)^(-3) η(10z)^(-1) η(12z) η(15z)^(-1) η(30z)^3`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^9 η(3z)^2 η(4z)^(-3) η(5z) η(6z)^(-3) η(10z)^(-1) η(12z) η(15z)^(-1) η(30z)^3` at level 180. -/
abbrev cuspForm_180_eta_1m4_2p9_3p2_4m3_5p1_6m3_10m1_12p1_15m1_30p3 : gamma0CuspForms 180 :=
  etaQuotientCuspForm 180 sparse![180; 0 => -4, 1 => 9, 2 => 2, 3 => -3, 4 => 1, 5 => -3, 9 => -1, 11 => 1, 14 => -1, 29 => 3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_180_eta_1m4_2p9_3p2_4m3_5p1_6m3_10m1_12p1_15m1_30p3_first_coeffs :
    first_coeffs 100 cuspForm_180_eta_1m4_2p9_3p2_4m3_5p1_6m3_10m1_12p1_15m1_30p3 =
    [0, 0, 0, 1, 4, 5, 2, 1, 1, 0, 1, 2, 3, -1, -4, 0, -2, -1, 3, 2,
     0, -2, 1, 0, -2, 0, 4, 1, -5, -2, -3, -2, -4, -2, -8, -19, -8, -3, 1, 0,
     -1, -2, -10, 2, 10, -1, 0, -1, -9, -4, 0, 4, -3, -1, 2, -1, -4, 0, 8, 2,
     8, 2, 8, -2, 0, 9, 2, 4, -11, 0, -5, -2, 7, 2, -6, 1, 6, 3, 6, -2,
     3, 0, 5, 3, 10, 2, -8, -4, 9, 6, -2, 2, 0, 4, -2, 39, 18, 0, 7, 2] := by
  eta_coeff

end WeightTwoCusps
