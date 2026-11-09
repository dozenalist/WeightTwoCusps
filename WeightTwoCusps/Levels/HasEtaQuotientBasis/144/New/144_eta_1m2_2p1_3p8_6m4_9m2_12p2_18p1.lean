module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 144

The eta expression is `η(z)^(-2) η(2z) η(3z)^8 η(6z)^(-4) η(9z)^(-2) η(12z)^2 η(18z)`; see
[the local level table](../../TABLE.md#level-144).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^8 η(6z)^(-4) η(9z)^(-2) η(12z)^2 η(18z)` at level 144. -/
abbrev cuspForm_144_eta_1m2_2p1_3p8_6m4_9m2_12p2_18p1 : gamma0CuspForms 144 :=
  etaQuotientCuspForm 144 sparse![144; 0 => -2, 1 => 1, 2 => 8, 5 => -4, 8 => -2, 11 => 2, 17 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_144_eta_1m2_2p1_3p8_6m4_9m2_12p2_18p1_first_coeffs :
    first_coeffs 100 cuspForm_144_eta_1m2_2p1_3p8_6m4_9m2_12p2_18p1 =
    [0, 1, 2, 4, 0, -2, -8, 0, 0, 4, -4, -4, 0, -2, 0, -8, 0, 2, 8, 4,
     0, 0, 8, 8, 0, -1, -4, 4, 0, 6, 16, -8, 0, -16, 4, 0, 0, 6, -8, -8,
     0, -6, 0, -4, 0, -8, -16, 0, 0, -7, -2, 8, 0, -2, -8, 8, 0, 16, 12, -4,
     0, -2, 16, 0, 0, 4, -32, 4, 0, 32, 0, -8, 0, 10, 12, -4, 0, 0, 16, 8,
     0, 4, -12, 4, 0, -4, 8, 24, 0, -6, -16, 0, 0, -32, 0, -8, 0, 2, -14, -16] := by
  eta_coeff

end WeightTwoCusps
