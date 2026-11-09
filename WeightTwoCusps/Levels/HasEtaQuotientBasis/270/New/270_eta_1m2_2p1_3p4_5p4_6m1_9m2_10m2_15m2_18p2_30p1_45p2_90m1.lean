module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-2) η(2z) η(3z)^4 η(5z)^4 η(6z)^(-1) η(9z)^(-2) η(10z)^(-2) η(15z)^(-2) η(18z)^2 η(30z) η(45z)^2 η(90z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^4 η(5z)^4 η(6z)^(-1) η(9z)^(-2) η(10z)^(-2) η(15z)^(-2) η(18z)^2 η(30z) η(45z)^2 η(90z)^(-1)` at level 270. -/
abbrev cuspForm_270_eta_1m2_2p1_3p4_5p4_6m1_9m2_10m2_15m2_18p2_30p1_45p2_90m1 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -2, 1 => 1, 2 => 4, 4 => 4, 5 => -1, 8 => -2, 9 => -2, 14 => -2, 17 => 2, 29 => 1, 44 => 2, 89 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m2_2p1_3p4_5p4_6m1_9m2_10m2_15m2_18p2_30p1_45p2_90m1_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m2_2p1_3p4_5p4_6m1_9m2_10m2_15m2_18p2_30p1_45p2_90m1 =
    [0, 1, 2, 4, 4, 6, 4, 3, -2, 0, 0, 2, 4, 7, 10, 0, 2, -4, 4, -5,
     6, 4, 6, 0, -4, 1, -8, 4, -6, 4, -4, 6, 2, 4, 6, -2, 0, -13, -8, -12,
     2, 4, -4, -2, 2, -4, -18, -4, 0, -4, -16, -8, -8, -10, -8, -4, -14, -12, -6, -16,
     0, 1, 10, -8, -10, -16, -12, -3, -4, 0, -6, 16, -12, -11, 4, 4, -2, -18, -4, -15,
     -2, 0, 12, 6, 4, 2, -20, 8, 10, 12, 8, 9, 0, -8, 6, 8, 4, 5, 24, 8] := by
  eta_coeff

end WeightTwoCusps
