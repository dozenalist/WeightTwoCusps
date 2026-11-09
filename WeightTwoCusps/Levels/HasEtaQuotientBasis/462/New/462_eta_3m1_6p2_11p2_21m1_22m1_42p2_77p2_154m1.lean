module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 462

The eta expression is `η(3z)^(-1) η(6z)^2 η(11z)^2 η(21z)^(-1) η(22z)^(-1) η(42z)^2 η(77z)^2 η(154z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(3z)^(-1) η(6z)^2 η(11z)^2 η(21z)^(-1) η(22z)^(-1) η(42z)^2 η(77z)^2 η(154z)^(-1)` at level 462. -/
abbrev cuspForm_462_eta_3m1_6p2_11p2_21m1_22m1_42p2_77p2_154m1 : gamma0CuspForms 462 :=
  etaQuotientCuspForm 462 sparse![462; 2 => -1, 5 => 2, 10 => 2, 20 => -1, 21 => -1, 41 => 2, 76 => 2, 153 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_462_eta_3m1_6p2_11p2_21m1_22m1_42p2_77p2_154m1_first_coeffs :
    first_coeffs 100 cuspForm_462_eta_3m1_6p2_11p2_21m1_22m1_42p2_77p2_154m1 =
    [0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, -2, 0, 0, -2, 0, 0,
     0, 1, 0, -2, 1, 0, 0, 1, 0, 0, 0, 0, -2, 2, 0, -2, 0, 0, -2, 0,
     0, 0, 1, 0, -4, 0, 0, 2, 1, 0, 2, 0, 0, -2, 1, 0, 2, 0, 0, -2,
     0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0,
     -6, 0, 0, -2, 1, 0, 0, 2, 0, -2, 0, 4, 2, 0, 4, -2, 1, 0, -4, 0] := by
  eta_coeff

end WeightTwoCusps
