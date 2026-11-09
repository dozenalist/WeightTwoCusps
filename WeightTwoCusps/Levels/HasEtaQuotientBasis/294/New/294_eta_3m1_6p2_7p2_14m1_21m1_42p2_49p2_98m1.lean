module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 294

The eta expression is `η(3z)^(-1) η(6z)^2 η(7z)^2 η(14z)^(-1) η(21z)^(-1) η(42z)^2 η(49z)^2 η(98z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(3z)^(-1) η(6z)^2 η(7z)^2 η(14z)^(-1) η(21z)^(-1) η(42z)^2 η(49z)^2 η(98z)^(-1)` at level 294. -/
abbrev cuspForm_294_eta_3m1_6p2_7p2_14m1_21m1_42p2_49p2_98m1 : gamma0CuspForms 294 :=
  etaQuotientCuspForm 294 sparse![294; 2 => -1, 5 => 2, 6 => 2, 13 => -1, 20 => -1, 41 => 2, 48 => 2, 97 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_294_eta_3m1_6p2_7p2_14m1_21m1_42p2_49p2_98m1_first_coeffs :
    first_coeffs 100 cuspForm_294_eta_3m1_6p2_7p2_14m1_21m1_42p2_49p2_98m1 =
    [0, 0, 0, 1, 0, 0, 1, 0, 0, 0, -2, 0, 1, -2, 0, 0, 0, 0, 0, -2,
     0, 1, 0, 0, 1, 0, 0, 1, -2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0,
     -2, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, -2, 0, 0, 0, 4,
     0, 0, 4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, -6, 0, -1, -4, 4, 0, 0,
     0, 0, -4, 0, -1, 0, 0, 0, 0, 4, -2, -4, 0, 0, 0, 0, -3, 2, 0, 0] := by
  eta_coeff

end WeightTwoCusps
