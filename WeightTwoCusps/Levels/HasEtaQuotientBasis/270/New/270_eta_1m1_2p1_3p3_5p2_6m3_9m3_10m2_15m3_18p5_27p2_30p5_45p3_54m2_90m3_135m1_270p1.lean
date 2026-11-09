module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-1) η(2z) η(3z)^3 η(5z)^2 η(6z)^(-3) η(9z)^(-3) η(10z)^(-2) η(15z)^(-3) η(18z)^5 η(27z)^2 η(30z)^5 η(45z)^3 η(54z)^(-2) η(90z)^(-3) η(135z)^(-1) η(270z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z)^3 η(5z)^2 η(6z)^(-3) η(9z)^(-3) η(10z)^(-2) η(15z)^(-3) η(18z)^5 η(27z)^2 η(30z)^5 η(45z)^3 η(54z)^(-2) η(90z)^(-3) η(135z)^(-1) η(270z)` at level 270. -/
abbrev cuspForm_270_eta_1m1_2p1_3p3_5p2_6m3_9m3_10m2_15m3_18p5_27p2_30p5_45p3_54m2_90m3_135m1_270p1 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -1, 1 => 1, 2 => 3, 4 => 2, 5 => -3, 8 => -3, 9 => -2, 14 => -3, 17 => 5, 26 => 2, 29 => 5, 44 => 3, 53 => -2, 89 => -3, 134 => -1, 269 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m1_2p1_3p3_5p2_6m3_9m3_10m2_15m3_18p5_27p2_30p5_45p3_54m2_90m3_135m1_270p1_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m1_2p1_3p3_5p2_6m3_9m3_10m2_15m3_18p5_27p2_30p5_45p3_54m2_90m3_135m1_270p1 =
    [0, 0, 0, 0, 1, 1, 1, -1, -1, -2, -1, 0, 2, 3, 1, 1, -2, 0, -2, 0,
     -2, 0, 0, 1, 2, 1, 1, -2, 1, -2, 0, -3, 1, -3, 0, 1, 2, 2, -3, 0,
     -6, 2, -3, 3, -1, 2, 1, -2, 0, -5, 0, -3, 5, 0, 6, 0, 0, -6, -3, -1,
     0, 5, -1, 8, -4, 7, -4, 2, -4, 0, 2, -3, 6, -3, 10, 0, 8, -4, 1, -5,
     0, -2, 0, 6, 0, 6, -5, 6, -4, 7, -6, 2, 4, 0, 5, -7, -1, -7, 6, 0] := by
  eta_coeff

end WeightTwoCusps
