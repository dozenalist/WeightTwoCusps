module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 180

The eta expression is `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(6z)^(-2) η(12z) η(15z)^(-1) η(30z)^4 η(60z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(6z)^(-2) η(12z) η(15z)^(-1) η(30z)^4 η(60z)^(-1)` at level 180. -/
abbrev cuspForm_180_eta_1m4_2p10_3p1_4m4_6m2_12p1_15m1_30p4_60m1 : gamma0CuspForms 180 :=
  etaQuotientCuspForm 180 sparse![180; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 5 => -2, 11 => 1, 14 => -1, 29 => 4, 59 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_180_eta_1m4_2p10_3p1_4m4_6m2_12p1_15m1_30p4_60m1_first_coeffs :
    first_coeffs 100 cuspForm_180_eta_1m4_2p10_3p1_4m4_6m2_12p1_15m1_30p4_60m1 =
    [0, 0, 1, 4, 4, -1, 0, 4, 1, 0, 0, 2, 4, -4, -2, 0, -4, 2, 4, 8,
     -1, -8, 4, 0, 0, 0, 0, 4, -4, -2, -4, -8, -3, -8, -8, 2, -8, -12, 0, 0,
     0, -8, -8, 8, 6, -4, 0, -4, -12, -16, 1, 16, -4, 2, 0, -4, -2, 0, 8, 2,
     8, 8, 4, -8, 4, 0, 8, 16, -6, 0, -4, 4, 4, 8, -4, 4, 8, 0, 8, -8,
     3, 0, -4, 0, 8, 8, 0, -16, 4, 12, 0, 8, 0, 16, -8, 0, 16, 0, 1, 8] := by
  eta_coeff

end WeightTwoCusps
