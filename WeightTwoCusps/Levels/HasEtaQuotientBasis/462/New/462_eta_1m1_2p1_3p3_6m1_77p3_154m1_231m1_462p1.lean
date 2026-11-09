module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 462

The eta expression is `η(z)^(-1) η(2z) η(3z)^3 η(6z)^(-1) η(77z)^3 η(154z)^(-1) η(231z)^(-1) η(462z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z)^3 η(6z)^(-1) η(77z)^3 η(154z)^(-1) η(231z)^(-1) η(462z)` at level 462. -/
abbrev cuspForm_462_eta_1m1_2p1_3p3_6m1_77p3_154m1_231m1_462p1 : gamma0CuspForms 462 :=
  etaQuotientCuspForm 462 sparse![462; 0 => -1, 1 => 1, 2 => 3, 5 => -1, 76 => 3, 153 => -1, 230 => -1, 461 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_462_eta_1m1_2p1_3p3_6m1_77p3_154m1_231m1_462p1_first_coeffs :
    first_coeffs 100 cuspForm_462_eta_1m1_2p1_3p3_6m1_77p3_154m1_231m1_462p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, -1, -1, 0, -1,
     0, -2, 0, -1, -1, 1, -1, 0, 1, 1, 1, -2, 0, 1, 0, 3, 1, 0, -1, 2,
     1, 0, -1, 1, 0, -1, 1, 0, 1, 0, 0, -2, 0, 1, -1, 0, -1, 0, -1, -2,
     0, -1, 0, 0, 0, -1, 0, -1, 1, 1, -1, -1, 0, -2, 1, -1, -1, 0, 0, 2,
     0, 1, 0, 1, -1, 2, 0, 0, 0, -2, -2, 0, -2, 2, 4, 0, 3, 0, 7, 0] := by
  eta_coeff

end WeightTwoCusps
