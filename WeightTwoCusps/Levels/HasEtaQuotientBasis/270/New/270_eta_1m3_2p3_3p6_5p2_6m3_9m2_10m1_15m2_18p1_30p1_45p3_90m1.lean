module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-3) η(2z)^3 η(3z)^6 η(5z)^2 η(6z)^(-3) η(9z)^(-2) η(10z)^(-1) η(15z)^(-2) η(18z) η(30z) η(45z)^3 η(90z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^3 η(3z)^6 η(5z)^2 η(6z)^(-3) η(9z)^(-2) η(10z)^(-1) η(15z)^(-2) η(18z) η(30z) η(45z)^3 η(90z)^(-1)` at level 270. -/
abbrev cuspForm_270_eta_1m3_2p3_3p6_5p2_6m3_9m2_10m1_15m2_18p1_30p1_45p3_90m1 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -3, 1 => 3, 2 => 6, 4 => 2, 5 => -3, 8 => -2, 9 => -1, 14 => -2, 17 => 1, 29 => 1, 44 => 3, 89 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m3_2p3_3p6_5p2_6m3_9m2_10m1_15m2_18p1_30p1_45p3_90m1_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m3_2p3_3p6_5p2_6m3_9m2_10m1_15m2_18p1_30p1_45p3_90m1 =
    [0, 0, 1, 3, 6, 7, 6, 4, 1, 0, -2, 2, 3, 4, 2, 0, 2, -1, 6, 2,
     6, 0, 4, 1, -6, 2, -2, 6, -12, 0, -3, 2, 2, 6, 10, -6, 0, -12, -1, -6,
     12, 2, -6, -8, -2, -6, -14, -4, -3, -2, -21, -12, -16, -5, -12, -4, -8, -6, -8, -8,
     0, -6, 3, -12, -14, -24, 0, 0, -2, 0, -2, 6, -18, 0, 2, 3, 0, -8, -6, -12,
     3, 0, 12, 3, 0, -4, -8, 12, 12, 6, 12, -2, 4, 0, -2, 13, 6, 20, 5, 12] := by
  eta_coeff

end WeightTwoCusps
