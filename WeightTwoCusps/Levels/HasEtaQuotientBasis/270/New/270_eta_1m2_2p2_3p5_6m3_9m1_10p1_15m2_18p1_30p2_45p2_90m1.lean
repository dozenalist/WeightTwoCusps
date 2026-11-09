module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^5 η(6z)^(-3) η(9z)^(-1) η(10z) η(15z)^(-2) η(18z) η(30z)^2 η(45z)^2 η(90z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^5 η(6z)^(-3) η(9z)^(-1) η(10z) η(15z)^(-2) η(18z) η(30z)^2 η(45z)^2 η(90z)^(-1)` at level 270. -/
abbrev cuspForm_270_eta_1m2_2p2_3p5_6m3_9m1_10p1_15m2_18p1_30p2_45p2_90m1 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -2, 1 => 2, 2 => 5, 5 => -3, 8 => -1, 9 => 1, 14 => -2, 17 => 1, 29 => 2, 44 => 2, 89 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m2_2p2_3p5_6m3_9m1_10p1_15m2_18p1_30p2_45p2_90m1_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m2_2p2_3p5_6m3_9m1_10p1_15m2_18p1_30p2_45p2_90m1 =
    [0, 0, 1, 2, 3, 1, -1, -1, 0, 3, 0, 0, -4, -4, -1, 0, 4, 0, 2, 1,
     -1, -1, -1, -1, -2, -5, 0, -4, -3, -2, 1, 4, 0, 8, -1, -1, -9, 0, -1, -3,
     -2, -1, -2, -4, 1, 4, 5, 0, 6, -7, -1, -7, 10, 1, -1, 1, 0, 6, -4, 4,
     3, 3, -2, 2, -4, 3, -3, 12, 4, 0, 1, 1, 6, -9, 5, 2, 6, -1, 4, 9,
     3, 3, 6, 3, -1, 1, 3, -2, -15, 0, 1, 8, -4, 2, 2, -4, 5, -5, -2, -14] := by
  eta_coeff

end WeightTwoCusps
