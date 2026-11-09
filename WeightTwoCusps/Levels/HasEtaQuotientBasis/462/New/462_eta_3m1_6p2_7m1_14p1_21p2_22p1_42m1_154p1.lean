module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 462

The eta expression is `η(3z)^(-1) η(6z)^2 η(7z)^(-1) η(14z) η(21z)^2 η(22z) η(42z)^(-1) η(154z)`; see
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

/-- The cuspidal eta quotient `η(3z)^(-1) η(6z)^2 η(7z)^(-1) η(14z) η(21z)^2 η(22z) η(42z)^(-1) η(154z)` at level 462. -/
abbrev cuspForm_462_eta_3m1_6p2_7m1_14p1_21p2_22p1_42m1_154p1 : gamma0CuspForms 462 :=
  etaQuotientCuspForm 462 sparse![462; 2 => -1, 5 => 2, 6 => -1, 13 => 1, 20 => 2, 21 => 1, 41 => -1, 153 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_462_eta_3m1_6p2_7m1_14p1_21p2_22p1_42m1_154p1_first_coeffs :
    first_coeffs 100 cuspForm_462_eta_3m1_6p2_7m1_14p1_21p2_22p1_42m1_154p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0,
     0, 0, 1, 0, 1, 1, 1, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, -1, 1, -1,
     0, 0, 0, 1, -1, 1, 0, -1, -1, 0, 0, 0, 1, 0, 0, -2, 0, 1, 0, -1,
     1, 0, -2, 0, 0, -1, 0, 0, -2, -1, -1, 1, 0, 1, -2, -1, 0, -1, 1, -1,
     0, 0, -3, -1, -1, 1, 0, 0, 0, -2, -1, 0, 2, -1, 0, 0, -2, -2, 0, 1] := by
  eta_coeff

end WeightTwoCusps
