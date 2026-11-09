module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 204

The eta expression is `η(z)^(-3) η(2z)^8 η(3z) η(4z)^(-3) η(6z)^(-2) η(12z) η(17z)^(-3) η(34z)^8 η(51z) η(68z)^(-3) η(102z)^(-2) η(204z)`; see
[the local level table](../../TABLE.md#level-204).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^8 η(3z) η(4z)^(-3) η(6z)^(-2) η(12z) η(17z)^(-3) η(34z)^8 η(51z) η(68z)^(-3) η(102z)^(-2) η(204z)` at level 204. -/
abbrev cuspForm_204_eta_1m3_2p8_3p1_4m3_6m2_12p1_17m3_34p8_51p1_68m3_102m2_204p1 : gamma0CuspForms 204 :=
  etaQuotientCuspForm 204 sparse![204; 0 => -3, 1 => 8, 2 => 1, 3 => -3, 5 => -2, 11 => 1, 16 => -3, 33 => 8, 50 => 1, 67 => -3, 101 => -2, 203 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_204_eta_1m3_2p8_3p1_4m3_6m2_12p1_17m3_34p8_51p1_68m3_102m2_204p1_first_coeffs :
    first_coeffs 100 cuspForm_204_eta_1m3_2p8_3p1_4m3_6m2_12p1_17m3_34p8_51p1_68m3_102m2_204p1 =
    [0, 0, 0, 1, 3, 1, -3, -1, 0, -1, 0, -2, 0, -1, -3, 1, -3, 0, 3, 1,
     6, 7, 3, -8, -3, 3, 0, 0, -9, 2, 0, -9, 0, -8, 0, 8, 6, 10, 0, 1,
     0, -3, 9, 9, -3, -11, 3, 8, -6, -10, 0, -1, 0, 10, 0, -3, -3, 9, 0, 4,
     6, -10, 3, -9, 9, -1, -15, 10, -3, -8, 0, -9, 3, 0, -6, 10, -6, -16, -6, 9,
     -12, 4, 0, -4, 3, -1, 6, -10, 3, -8, 0, -10, 15, -1, -6, 11, -3, 14, 6, 16] := by
  eta_coeff

end WeightTwoCusps
