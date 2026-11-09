module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^5 η(5z) η(6z)^(-3) η(9z)^(-3) η(10z)^(-1) η(15z)^(-3) η(18z)^2 η(27z)^2 η(30z)^3 η(45z)^6 η(54z)^(-1) η(90z)^(-3) η(135z)^(-2) η(270z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^5 η(5z) η(6z)^(-3) η(9z)^(-3) η(10z)^(-1) η(15z)^(-3) η(18z)^2 η(27z)^2 η(30z)^3 η(45z)^6 η(54z)^(-1) η(90z)^(-3) η(135z)^(-2) η(270z)` at level 270. -/
abbrev cuspForm_270_eta_1m2_2p2_3p5_5p1_6m3_9m3_10m1_15m3_18p2_27p2_30p3_45p6_54m1_90m3_135m2_270p1 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -2, 1 => 2, 2 => 5, 4 => 1, 5 => -3, 8 => -3, 9 => -1, 14 => -3, 17 => 2, 26 => 2, 29 => 3, 44 => 6, 53 => -1, 89 => -3, 134 => -2, 269 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m2_2p2_3p5_5p1_6m3_9m3_10m1_15m3_18p2_27p2_30p3_45p6_54m1_90m3_135m2_270p1_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m2_2p2_3p5_5p1_6m3_9m3_10m1_15m3_18p2_27p2_30p3_45p6_54m1_90m3_135m2_270p1 =
    [0, 0, 1, 2, 3, 1, -1, -2, -2, 0, -1, 3, 2, 4, 1, -1, -1, -2, 4, 0,
     4, 0, 6, -1, -3, -4, -1, 4, -2, 5, -2, 8, -2, 4, -5, 0, 0, -2, 1, -4,
     12, -1, 4, -14, 0, -4, -1, -2, -2, 6, -3, 4, -8, 1, -8, 4, -8, -4, -4, -2,
     -1, -12, 2, -8, 2, -10, 0, -4, -2, 0, -4, -1, -12, -4, -9, 2, -3, 3, -2, 0,
     -2, 0, -4, -7, 0, -6, 2, -10, 14, 4, 8, -4, -4, 0, -8, 3, -1, 14, 8, 8] := by
  eta_coeff

end WeightTwoCusps
