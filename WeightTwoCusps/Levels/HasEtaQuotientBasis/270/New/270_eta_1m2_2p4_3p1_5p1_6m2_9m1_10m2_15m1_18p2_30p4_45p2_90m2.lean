module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 270

The eta expression is `η(z)^(-2) η(2z)^4 η(3z) η(5z) η(6z)^(-2) η(9z)^(-1) η(10z)^(-2) η(15z)^(-1) η(18z)^2 η(30z)^4 η(45z)^2 η(90z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z) η(5z) η(6z)^(-2) η(9z)^(-1) η(10z)^(-2) η(15z)^(-1) η(18z)^2 η(30z)^4 η(45z)^2 η(90z)^(-2)` at level 270. -/
abbrev cuspForm_270_eta_1m2_2p4_3p1_5p1_6m2_9m1_10m2_15m1_18p2_30p4_45p2_90m2 : gamma0CuspForms 270 :=
  etaQuotientCuspForm 270 sparse![270; 0 => -2, 1 => 4, 2 => 1, 4 => 1, 5 => -2, 8 => -1, 9 => -2, 14 => -1, 17 => 2, 29 => 4, 44 => 2, 89 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_270_eta_1m2_2p4_3p1_5p1_6m2_9m1_10m2_15m1_18p2_30p4_45p2_90m2_first_coeffs :
    first_coeffs 100 cuspForm_270_eta_1m2_2p4_3p1_5p1_6m2_9m1_10m2_15m1_18p2_30p4_45p2_90m2 =
    [0, 1, 2, 1, 1, 0, -2, 0, 1, 0, 0, 2, 1, 1, 4, 0, -1, -1, -2, -2,
     0, 4, 3, 3, 2, 1, -2, -2, 0, -2, -1, 3, -1, -2, 3, 1, 0, -4, -2, -6,
     -1, 4, 2, 1, -4, 2, -9, -4, 3, -1, -1, 4, 1, -7, 4, -1, -8, -6, -3, -10,
     0, 4, 4, 4, -1, 2, -12, -6, -7, 0, -3, 4, 6, -8, 4, 1, -2, -6, 2, -9,
     -5, 0, 6, 3, 4, 5, -14, -4, 1, 12, -4, 12, 3, -8, 3, -1, -2, -4, 12, -4] := by
  eta_coeff

end WeightTwoCusps
