module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 462

The eta expression is `η(z)^(-1) η(2z)^2 η(3z) η(6z)^(-1) η(11z)^2 η(21z)^2 η(22z)^(-1) η(33z)^(-1) η(42z)^(-1) η(66z) η(231z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(3z) η(6z)^(-1) η(11z)^2 η(21z)^2 η(22z)^(-1) η(33z)^(-1) η(42z)^(-1) η(66z) η(231z)` at level 462. -/
abbrev cuspForm_462_eta_1m1_2p2_3p1_6m1_11p2_21p2_22m1_33m1_42m1_66p1_231p1 : gamma0CuspForms 462 :=
  etaQuotientCuspForm 462 sparse![462; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 10 => 2, 20 => 2, 21 => -1, 32 => -1, 41 => -1, 65 => 1, 230 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_462_eta_1m1_2p2_3p1_6m1_11p2_21p2_22m1_33m1_42m1_66p1_231p1_first_coeffs :
    first_coeffs 100 cuspForm_462_eta_1m1_2p2_3p1_6m1_11p2_21p2_22m1_33m1_42m1_66p1_231p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 0, 0, 0, 0,
     -2, 0, -2, -2, 0, 0, 2, -1, 0, 0, 0, 4, -2, -2, 0, 0, 3, 0, 2, 0,
     0, 4, 0, 4, 5, 1, 0, -4, 1, 0, 0, 0, -8, -2, 0, 0, 0, -2, -4, -4,
     0, 0, 0, 0, 0, -2, -2, 0, 0, 3, 0, -2, 0, 0, 4, -1, 0, 1, 1, 8,
     2, -1, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 2, 0, 0, 2, 4, 0, -2, -4] := by
  eta_coeff

end WeightTwoCusps
