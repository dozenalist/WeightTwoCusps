module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 462

The eta expression is `η(3z)^(-1) η(6z)^2 η(11z) η(14z) η(21z) η(22z)^(-1) η(42z)^(-1) η(66z) η(77z)^(-1) η(154z)^2`; see
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

/-- The cuspidal eta quotient `η(3z)^(-1) η(6z)^2 η(11z) η(14z) η(21z) η(22z)^(-1) η(42z)^(-1) η(66z) η(77z)^(-1) η(154z)^2` at level 462. -/
abbrev cuspForm_462_eta_3m1_6p2_11p1_14p1_21p1_22m1_42m1_66p1_77m1_154p2 : gamma0CuspForms 462 :=
  etaQuotientCuspForm 462 sparse![462; 2 => -1, 5 => 2, 10 => 1, 13 => 1, 20 => 1, 21 => -1, 41 => -1, 65 => 1, 76 => -1, 153 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_462_eta_3m1_6p2_11p1_14p1_21p1_22m1_42m1_66p1_77m1_154p2_first_coeffs :
    first_coeffs 100 cuspForm_462_eta_3m1_6p2_11p1_14p1_21p1_22m1_42m1_66p1_77m1_154p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0,
     0, 1, 0, -1, 0, 0, -2, 0, 0, -1, 1, 0, -1, -1, 0, -1, -1, 1, 0, 0,
     0, -1, 0, -1, 0, -1, 1, 2, -1, -1, 1, 0, 0, 0, 0, 1, 1, 1, -2, 2,
     1, 0, 2, -2, 1, 2, 1, -1, 0, 2, -2, -1, -1, 0, 2, -1, -1, 1, -2, 0,
     -2, 1, 3, -1, 0, -1, 0, -1, -1, 3, -1, 5, 3, -3, 0, 1, 2, -1, 2, 2] := by
  eta_coeff

end WeightTwoCusps
