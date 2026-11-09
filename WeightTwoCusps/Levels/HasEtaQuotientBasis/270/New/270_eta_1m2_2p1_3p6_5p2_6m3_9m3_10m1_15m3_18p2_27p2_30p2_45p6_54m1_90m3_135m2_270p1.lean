module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-2) η(2z) η(3z)^6 η(5z)^2 η(6z)^(-3) η(9z)^(-3) η(10z)^(-1) η(15z)^(-3) η(18z)^2 η(27z)^2 η(30z)^2 η(45z)^6 η(54z)^(-1) η(90z)^(-3) η(135z)^(-2) η(270z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^6 η(5z)^2 η(6z)^(-3) η(9z)^(-3) η(10z)^(-1) η(15z)^(-3) η(18z)^2 η(27z)^2 η(30z)^2 η(45z)^6 η(54z)^(-1) η(90z)^(-3) η(135z)^(-2) η(270z)` at level 270. -/
abbrev cuspForm_270_eta_1m2_2p1_3p6_5p2_6m3_9m3_10m1_15m3_18p2_27p2_30p2_45p6_54m1_90m3_135m2_270p1 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -2, 1 => 1, 2 => 6, 4 => 2, 5 => -3, 8 => -3, 9 => -1, 14 => -3, 17 => 2, 26 => 2, 29 => 2, 44 => 6, 53 => -1, 89 => -3, 134 => -2, 269 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m2_2p1_3p6_5p2_6m3_9m3_10m1_15m3_18p2_27p2_30p2_45p6_54m1_90m3_135m2_270p1_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m2_2p1_3p6_5p2_6m3_9m3_10m1_15m3_18p2_27p2_30p2_45p6_54m1_90m3_135m2_270p1 =
    [0, 1, 2, 4, 2, 2, -2, 0, -4, 0, 1, 6, 4, 0, 2, -2, 3, -4, 8, 3,
     8, 0, 0, -2, -6, 3, -2, 8, -2, 10, -4, 1, -4, 8, 5, 0, 0, -2, 2, -8,
     3, -2, 8, -6, 0, -8, -3, -4, -4, -1, -6, 8, -6, 2, -16, 0, -16, -8, -10, -4,
     -2, -13, 4, -16, -3, -20, 0, -6, -4, 0, -8, -2, -24, -6, -18, 4, -6, 6, -4, -7,
     -4, 0, 0, -14, 0, -5, 4, -20, 6, 8, 16, -2, -8, 0, -4, 6, -2, 16, 16, 16] := by
  eta_coeff

end WeightTwoCusps
