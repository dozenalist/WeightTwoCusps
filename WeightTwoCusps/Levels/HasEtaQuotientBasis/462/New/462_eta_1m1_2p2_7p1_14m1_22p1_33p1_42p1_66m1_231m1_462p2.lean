module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 462

The eta expression is `η(z)^(-1) η(2z)^2 η(7z) η(14z)^(-1) η(22z) η(33z) η(42z) η(66z)^(-1) η(231z)^(-1) η(462z)^2`; see
[the local level table](../../TABLE.md#level-462).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(7z) η(14z)^(-1) η(22z) η(33z) η(42z) η(66z)^(-1) η(231z)^(-1) η(462z)^2` at level 462. -/
abbrev cuspForm_462_eta_1m1_2p2_7p1_14m1_22p1_33p1_42p1_66m1_231m1_462p2 : gamma0CuspForms 462 :=
  etaQuotientCuspForm 462 sparse![462; 0 => -1, 1 => 2, 6 => 1, 13 => -1, 21 => 1, 32 => 1, 41 => 1, 65 => -1, 230 => -1, 461 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_462_eta_1m1_2p2_7p1_14m1_22p1_33p1_42p1_66m1_231m1_462p2_first_coeffs :
    first_coeffs 100 cuspForm_462_eta_1m1_2p2_7p1_14m1_22p1_33p1_42p1_66m1_231m1_462p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, -1, -1, 0,
     0, 0, 0, -1, 0, 1, 0, -1, 0, 0, 0, 0, -3, -1, -1, -1, 0, -1, 0, 2,
     1, 0, 0, -1, 0, -1, -2, -1, 0, 0, 1, 0, -1, 0, 1, -1, 2, -1, -1, 1,
     -2, 0, 0, 0, 0, 4, 2, 5, 2, 1, 1, 1, -1, -2, 1, 0, 3, -1, 2, 0] := by
  eta_coeff

end WeightTwoCusps
