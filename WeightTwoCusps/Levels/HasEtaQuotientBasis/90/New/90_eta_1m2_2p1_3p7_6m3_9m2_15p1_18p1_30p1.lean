module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 90

The eta expression is `η(z)^(-2) η(2z) η(3z)^7 η(6z)^(-3) η(9z)^(-2) η(15z) η(18z) η(30z)`; see
[the local level table](../../TABLE.md#level-90).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^7 η(6z)^(-3) η(9z)^(-2) η(15z) η(18z) η(30z)` at level 90. -/
abbrev cuspForm_90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1 : gamma0CuspForms 90 :=
  etaQuotientCuspForm 90 sparse![90; 0 => -2, 1 => 1, 2 => 7, 5 => -3, 8 => -2, 14 => 1, 17 => 1, 29 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1_first_coeffs :
    first_coeffs 100 cuspForm_90_eta_1m2_2p1_3p7_6m3_9m2_15p1_18p1_30p1 =
    [0, 0, 1, 2, 4, 1, 0, -4, 1, 0, 0, -2, -2, 4, -2, 0, -4, -2, -2, -8,
     -1, -4, 4, 0, 0, 0, 0, 2, -4, 2, 2, 8, -3, -4, -8, -2, 4, 12, 0, 0,
     0, 8, 4, -8, 6, -2, 0, 4, 6, 16, 1, 8, -4, -2, 0, 4, -2, 0, 8, -2,
     -4, -8, 4, -4, 4, 0, -4, -16, -6, 0, -4, -4, -2, -8, -4, 2, 8, 0, -4, 8,
     3, 0, -4, 0, -4, -8, 0, -8, 4, -12, 0, -8, 0, 8, -8, 0, -8, 0, 1, 4] := by
  eta_coeff

end WeightTwoCusps
