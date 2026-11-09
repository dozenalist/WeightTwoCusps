module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 462

The eta expression is `η(z)^(-1) η(2z)^2 η(3z) η(6z)^(-1) η(7z)^2 η(14z)^(-1) η(21z)^(-1) η(33z)^(-1) η(42z) η(66z)^2 η(231z)^2 η(462z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(3z) η(6z)^(-1) η(7z)^2 η(14z)^(-1) η(21z)^(-1) η(33z)^(-1) η(42z) η(66z)^2 η(231z)^2 η(462z)^(-1)` at level 462. -/
abbrev cuspForm_462_eta_1m1_2p2_3p1_6m1_7p2_14m1_21m1_33m1_42p1_66p2_231p2_462m1 : gamma0CuspForms 462 :=
  etaQuotientCuspForm 462 sparse![462; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 6 => 2, 13 => -1, 20 => -1, 32 => -1, 41 => 1, 65 => 2, 230 => 2, 461 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_462_eta_1m1_2p2_3p1_6m1_7p2_14m1_21m1_33m1_42p1_66p2_231p2_462m1_first_coeffs :
    first_coeffs 100 cuspForm_462_eta_1m1_2p2_3p1_6m1_7p2_14m1_21m1_33m1_42p1_66p2_231p2_462m1 =
    [0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, 0, -2, -2, -2, 0, 2, 0, 0, 0,
     0, 3, 0, 0, 0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, -2, 0, -2, 1, 1,
     0, 2, -2, 0, 0, -2, -2, -1, -3, 2, 0, 0, 0, 0, 4, 0, -2, 0, 0, 1,
     1, 0, 2, -1, 0, 0, 0, 0, -2, -1, -2, 0, 1, 0, 2, -2, 0, 0, 0, 2,
     1, -3, 0, 2, 4, 0, -2, 1, 0, -2, -1, 2, 0, 4, -2, 2, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
