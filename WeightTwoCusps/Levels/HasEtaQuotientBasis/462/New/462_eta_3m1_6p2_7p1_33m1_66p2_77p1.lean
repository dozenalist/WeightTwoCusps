module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 462

The eta expression is `η(3z)^(-1) η(6z)^2 η(7z) η(33z)^(-1) η(66z)^2 η(77z)`; see
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

/-- The cuspidal eta quotient `η(3z)^(-1) η(6z)^2 η(7z) η(33z)^(-1) η(66z)^2 η(77z)` at level 462. -/
abbrev cuspForm_462_eta_3m1_6p2_7p1_33m1_66p2_77p1 : gamma0CuspForms 462 :=
  etaQuotientCuspForm 462 sparse![462; 2 => -1, 5 => 2, 6 => 1, 32 => -1, 65 => 2, 76 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_462_eta_3m1_6p2_7p1_33m1_66p2_77p1_first_coeffs :
    first_coeffs 100 cuspForm_462_eta_3m1_6p2_7p1_33m1_66p2_77p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, -1, 0, 1, -1, 0,
     0, 0, -1, 0, -1, -1, 1, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 1, 0,
     -1, 1, 0, 1, 1, -1, 1, 0, -1, 0, 1, -1, 0, 1, 0, -1, 0, 0, -1, 1,
     0, 1, 0, 0, -1, 0, 0, -1, 0, 0, 0, 2, 0, 0, 0, 1, 1, 0, -2, 1,
     0, 0, 0, 0, 0, -2, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1] := by
  eta_coeff

end WeightTwoCusps
