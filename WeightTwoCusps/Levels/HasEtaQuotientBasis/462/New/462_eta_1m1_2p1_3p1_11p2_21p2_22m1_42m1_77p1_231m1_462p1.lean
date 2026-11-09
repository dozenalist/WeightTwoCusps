module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 462

The eta expression is `η(z)^(-1) η(2z) η(3z) η(11z)^2 η(21z)^2 η(22z)^(-1) η(42z)^(-1) η(77z) η(231z)^(-1) η(462z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z) η(11z)^2 η(21z)^2 η(22z)^(-1) η(42z)^(-1) η(77z) η(231z)^(-1) η(462z)` at level 462. -/
abbrev cuspForm_462_eta_1m1_2p1_3p1_11p2_21p2_22m1_42m1_77p1_231m1_462p1 : gamma0CuspForms 462 :=
  etaQuotientCuspForm 462 sparse![462; 0 => -1, 1 => 1, 2 => 1, 10 => 2, 20 => 2, 21 => -1, 41 => -1, 76 => 1, 230 => -1, 461 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_462_eta_1m1_2p1_3p1_11p2_21p2_22m1_42m1_77p1_231m1_462p1_first_coeffs :
    first_coeffs 100 cuspForm_462_eta_1m1_2p1_3p1_11p2_21p2_22m1_42m1_77p1_231m1_462p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 1,
     2, 2, 2, 3, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 0, 1, 1, 2, 1, -2,
     1, 0, -1, 1, -2, 1, 1, 2, 1, -2, 2, -2, 0, 1, -3, 0, -1, 0, -1, -2,
     2, -1, 0, 0, -4, -1, 0, 1, -1, -3, -1, -1, 2, 0, -3, 3, -1, -2, -2, -4,
     0, -3, 0, -5, -3, -2, -4, 0, -2, -4, -4, -4, -2, -8, -6, -4, -7, 0, -1, -6] := by
  eta_coeff

end WeightTwoCusps
