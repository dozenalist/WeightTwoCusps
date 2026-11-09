module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 462

The eta expression is `η(z)^(-1) η(2z) η(3z)^3 η(6z)^(-2) η(7z) η(11z) η(14z)^(-1) η(21z)^(-2) η(22z)^(-1) η(33z)^(-1) η(42z)^3 η(66z)^2 η(77z)^(-1) η(154z) η(231z)^2 η(462z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z)^3 η(6z)^(-2) η(7z) η(11z) η(14z)^(-1) η(21z)^(-2) η(22z)^(-1) η(33z)^(-1) η(42z)^3 η(66z)^2 η(77z)^(-1) η(154z) η(231z)^2 η(462z)^(-1)` at level 462. -/
abbrev cuspForm_462_eta_1m1_2p1_3p3_6m2_7p1_11p1_14m1_21m2_22m1_33m1_42p3_66p2_77m1_154p1_231p2_462m1 : gamma0CuspForms 462 :=
  etaQuotientCuspForm 462 sparse![462; 0 => -1, 1 => 1, 2 => 3, 5 => -2, 6 => 1, 10 => 1, 13 => -1, 20 => -2, 21 => -1, 32 => -1, 41 => 3, 65 => 2, 76 => -1, 153 => 1, 230 => 2, 461 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_462_eta_1m1_2p1_3p3_6m2_7p1_11p1_14m1_21m2_22m1_33m1_42p3_66p2_77m1_154p1_231p2_462m1_first_coeffs :
    first_coeffs 100 cuspForm_462_eta_1m1_2p1_3p3_6m2_7p1_11p1_14m1_21m2_22m1_33m1_42p3_66p2_77m1_154p1_231p2_462m1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, -1, -1, 0, 0, 0, -2, -2,
     -1, -1, 1, 0, 0, 1, -1, 2, 1, 2, 1, 0, 1, 1, 0, 2, 0, -1, -3, -3,
     0, 1, -1, -3, -3, 0, 3, 0, 3, 0, 1, 1, 1, 4, 2, -2, -1, -4, 4, 0,
     -2, -1, -3, 1, -1, 0, 1, -3, -1, 0, 2, 4, 0, 2, 0, 3, -2, -1, -2, 1,
     -4, -5, -1, 2, 2, -2, -4, 2, 1, 3, 0, -4, 4, -2, 5, 1, 2, 0, -1, 1] := by
  eta_coeff

end WeightTwoCusps
