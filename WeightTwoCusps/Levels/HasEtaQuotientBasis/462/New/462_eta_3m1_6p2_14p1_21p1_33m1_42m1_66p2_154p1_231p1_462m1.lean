module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 462

The eta expression is `η(3z)^(-1) η(6z)^2 η(14z) η(21z) η(33z)^(-1) η(42z)^(-1) η(66z)^2 η(154z) η(231z) η(462z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(3z)^(-1) η(6z)^2 η(14z) η(21z) η(33z)^(-1) η(42z)^(-1) η(66z)^2 η(154z) η(231z) η(462z)^(-1)` at level 462. -/
abbrev cuspForm_462_eta_3m1_6p2_14p1_21p1_33m1_42m1_66p2_154p1_231p1_462m1 : gamma0CuspForms 462 :=
  etaQuotientCuspForm 462 sparse![462; 2 => -1, 5 => 2, 13 => 1, 20 => 1, 32 => -1, 41 => -1, 65 => 2, 153 => 1, 230 => 1, 461 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_462_eta_3m1_6p2_14p1_21p1_33m1_42m1_66p2_154p1_231p1_462m1_first_coeffs :
    first_coeffs 100 cuspForm_462_eta_3m1_6p2_14p1_21p1_33m1_42m1_66p2_154p1_231p1_462m1 =
    [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, -1, 1,
     0, 0, -1, 0, -1, -1, 0, 0, 0, -1, 0, 0, -1, -1, 1, 0, 1, 1, -1, 1,
     -1, 0, 0, 1, 0, 0, 1, -1, -1, 0, 1, -1, 0, 1, 1, -1, 0, -1, -1, 0,
     -1, 0, -1, 0, 0, -1, 0, -2, 1, 1, 0, 0, 1, -2, 0, 0, 0, 0, 0, 1,
     1, 2, -1, 1, 0, 0, 1, 2, 1, 1, 0, 0, -1, -1, 0, 1, 1, 0, 0, 1] := by
  eta_coeff

end WeightTwoCusps
