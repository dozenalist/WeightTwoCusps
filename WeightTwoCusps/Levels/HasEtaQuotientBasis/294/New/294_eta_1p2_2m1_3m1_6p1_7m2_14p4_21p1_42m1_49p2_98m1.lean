module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 294

The eta expression is `η(z)^2 η(2z)^(-1) η(3z)^(-1) η(6z) η(7z)^(-2) η(14z)^4 η(21z) η(42z)^(-1) η(49z)^2 η(98z)^(-1)`; see
[the local level table](../../TABLE.md#level-294).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^2 η(2z)^(-1) η(3z)^(-1) η(6z) η(7z)^(-2) η(14z)^4 η(21z) η(42z)^(-1) η(49z)^2 η(98z)^(-1)` at level 294. -/
abbrev cuspForm_294_eta_1p2_2m1_3m1_6p1_7m2_14p4_21p1_42m1_49p2_98m1 : gamma0CuspForms 294 :=
  etaQuotientCuspForm 294 sparse![294; 0 => 2, 1 => -1, 2 => -1, 5 => 1, 6 => -2, 13 => 4, 20 => 1, 41 => -1, 48 => 2, 97 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_294_eta_1p2_2m1_3m1_6p1_7m2_14p4_21p1_42m1_49p2_98m1_first_coeffs :
    first_coeffs 100 cuspForm_294_eta_1p2_2m1_3m1_6p1_7m2_14p4_21p1_42m1_49p2_98m1 =
    [0, 1, -2, 0, 1, 0, 0, 1, 2, -4, 0, 0, 0, 0, 2, 1, -1, 0, -3, 0,
     0, 1, 2, 0, 0, -1, 0, 0, 1, 0, 1, 0, -2, 0, 0, 0, -4, 4, 0, -1,
     0, 0, -1, 0, 0, 0, 4, 0, 0, 1, -4, 4, 0, -2, 0, 0, -4, -5, 10, 0,
     1, 0, 0, -8, -1, 6, 0, 6, 0, 0, -6, -8, 3, 0, 6, 0, 0, -6, 1, -4,
     0, 9, 0, 0, 1, 4, -4, 0, 0, 0, 0, 2, 0, 2, 0, -4, 0, 0, -4, 4] := by
  eta_coeff

end WeightTwoCusps
