module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-2) η(2z) η(3z)^6 η(5z) η(6z)^(-3) η(9z)^(-1) η(10z) η(15z)^(-2) η(18z) η(30z) η(45z)^2 η(90z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^6 η(5z) η(6z)^(-3) η(9z)^(-1) η(10z) η(15z)^(-2) η(18z) η(30z) η(45z)^2 η(90z)^(-1)` at level 270. -/
abbrev cuspForm_270_eta_1m2_2p1_3p6_5p1_6m3_9m1_10p1_15m2_18p1_30p1_45p2_90m1 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -2, 1 => 1, 2 => 6, 4 => 1, 5 => -3, 8 => -1, 9 => 1, 14 => -2, 17 => 1, 29 => 1, 44 => 2, 89 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m2_2p1_3p6_5p1_6m3_9m1_10p1_15m2_18p1_30p1_45p2_90m1_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m2_2p1_3p6_5p1_6m3_9m1_10p1_15m2_18p1_30p1_45p2_90m1 =
    [0, 1, 2, 4, 2, 2, -1, 2, 0, 2, 1, 0, -4, -8, -2, 1, 5, 0, 4, -1,
     -2, -6, 2, -2, -3, -9, 0, -8, -8, -4, 2, 9, 0, 14, -1, -2, -14, 2, -2, -2,
     -3, -2, -6, -14, 2, 8, 7, 0, 8, -1, -2, -16, 6, 2, 2, 0, 0, 4, -6, 8,
     5, 15, -4, 12, 3, 6, -2, 10, 8, 0, 0, 2, 12, -12, 10, 4, 10, -2, 8, 13,
     6, 2, 8, 6, -6, -3, 6, -2, -8, 0, -2, 12, -8, 12, -4, -8, 7, -2, -4, -20] := by
  eta_coeff

end WeightTwoCusps
