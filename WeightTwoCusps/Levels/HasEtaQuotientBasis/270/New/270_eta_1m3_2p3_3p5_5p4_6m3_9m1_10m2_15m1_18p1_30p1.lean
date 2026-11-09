module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-3) η(2z)^3 η(3z)^5 η(5z)^4 η(6z)^(-3) η(9z)^(-1) η(10z)^(-2) η(15z)^(-1) η(18z) η(30z)`; see
[the local level table](../../TABLE.md#level-270).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^3 η(3z)^5 η(5z)^4 η(6z)^(-3) η(9z)^(-1) η(10z)^(-2) η(15z)^(-1) η(18z) η(30z)` at level 270. -/
abbrev cuspForm_270_eta_1m3_2p3_3p5_5p4_6m3_9m1_10m2_15m1_18p1_30p1 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -3, 1 => 3, 2 => 5, 4 => 4, 5 => -3, 8 => -1, 9 => -2, 14 => -1, 17 => 1, 29 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m3_2p3_3p5_5p4_6m3_9m1_10m2_15m1_18p1_30p1_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m3_2p3_3p5_5p4_6m3_9m1_10m2_15m1_18p1_30p1 =
    [0, 1, 3, 6, 8, 9, 8, 4, 0, -2, 1, 1, 2, 0, -1, -4, -3, 4, 0, -3,
     -14, -14, -20, -9, 2, 1, -5, -12, -2, -13, 0, 1, -4, -22, -23, -10, -10, 2, 7, 2,
     -11, -1, 2, -6, 0, 12, -3, -2, -2, 13, 3, 14, 34, 7, 14, -2, 8, -4, 26, 28,
     -2, 9, -4, 28, -1, 28, 14, -14, 0, 0, 22, 5, 24, 6, 3, 6, 10, -9, -18, -5,
     26, -2, 20, 15, -14, -5, -2, 40, -26, 6, -14, -4, -6, 28, 40, -41, 12, 8, -2, -20] := by
  eta_coeff

end WeightTwoCusps
