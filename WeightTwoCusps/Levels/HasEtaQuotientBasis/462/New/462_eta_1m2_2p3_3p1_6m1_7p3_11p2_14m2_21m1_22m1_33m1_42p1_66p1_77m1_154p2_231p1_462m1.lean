module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 462

The eta expression is `η(z)^(-2) η(2z)^3 η(3z) η(6z)^(-1) η(7z)^3 η(11z)^2 η(14z)^(-2) η(21z)^(-1) η(22z)^(-1) η(33z)^(-1) η(42z) η(66z) η(77z)^(-1) η(154z)^2 η(231z) η(462z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z) η(6z)^(-1) η(7z)^3 η(11z)^2 η(14z)^(-2) η(21z)^(-1) η(22z)^(-1) η(33z)^(-1) η(42z) η(66z) η(77z)^(-1) η(154z)^2 η(231z) η(462z)^(-1)` at level 462. -/
abbrev cuspForm_462_eta_1m2_2p3_3p1_6m1_7p3_11p2_14m2_21m1_22m1_33m1_42p1_66p1_77m1_154p2_231p1_462m1 : gamma0CuspForms 462 :=
  etaQuotientCuspForm 462 sparse![462; 0 => -2, 1 => 3, 2 => 1, 5 => -1, 6 => 3, 10 => 2, 13 => -2, 20 => -1, 21 => -1, 32 => -1, 41 => 1, 65 => 1, 76 => -1, 153 => 2, 230 => 1, 461 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_462_eta_1m2_2p3_3p1_6m1_7p3_11p2_14m2_21m1_22m1_33m1_42p1_66p1_77m1_154p2_231p1_462m1_first_coeffs :
    first_coeffs 100 cuspForm_462_eta_1m2_2p3_3p1_6m1_7p3_11p2_14m2_21m1_22m1_33m1_42p1_66p1_77m1_154p2_231p1_462m1 =
    [0, 0, 1, 2, 2, 3, 3, 4, 6, 4, 3, 3, 3, 4, 1, -1, -1, 0, 2, -3,
     -2, 2, 3, 5, -2, -1, 3, 2, 2, -8, -4, 5, 0, 3, -4, -2, 8, 3, 2, -4,
     1, 5, -4, -2, -9, -5, 5, -7, -2, -5, 0, 8, -4, -3, -7, -6, 3, -8, -9, -2,
     -3, 5, -5, -2, 3, 5, 3, -7, -3, 2, -4, -4, -12, -7, 5, -9, -2, -2, 3, 7,
     -5, -7, 2, 3, 6, -11, -6, 0, 1, 5, -4, 1, -1, 6, -2, -5, 2, 1, 0, 3] := by
  eta_coeff

end WeightTwoCusps
