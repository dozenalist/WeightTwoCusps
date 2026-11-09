module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 132

The eta expression is `η(z)^(-2) η(2z)^7 η(4z)^(-3) η(6z)^(-1) η(12z) η(33z)^2`; see
[the local level table](../../TABLE.md#level-132).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^7 η(4z)^(-3) η(6z)^(-1) η(12z) η(33z)^2` at level 132. -/
abbrev cuspForm_132_eta_1m2_2p7_4m3_6m1_12p1_33p2 : gamma0CuspForms 132 :=
  etaQuotientCuspForm 132 sparse![132; 0 => -2, 1 => 7, 3 => -3, 5 => -1, 11 => 1, 32 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_132_eta_1m2_2p7_4m3_6m1_12p1_33p2_first_coeffs :
    first_coeffs 100 cuspForm_132_eta_1m2_2p7_4m3_6m1_12p1_33p2 =
    [0, 0, 0, 1, 2, -2, -4, 2, 0, -3, 2, 0, 2, 2, -4, 1, 2, 0, 2, 4,
     0, -4, 0, -2, -2, 2, 0, -4, 2, 0, -4, 2, -4, 1, 4, 0, -2, -2, 4, 6,
     -2, -4, 8, -4, 0, -1, -2, 8, -6, 0, 0, -2, -6, 0, 6, 0, 4, 4, 0, -6,
     4, -2, 0, 4, -2, 8, -2, -6, -4, -3, -4, 2, 4, -4, 8, -4, 0, 0, -8, -2,
     4, 9, -8, 0, -6, -8, -4, 4, 0, 2, 4, -8, 12, 13, -2, -4, 14, -2, 4, -1] := by
  eta_coeff

end WeightTwoCusps
