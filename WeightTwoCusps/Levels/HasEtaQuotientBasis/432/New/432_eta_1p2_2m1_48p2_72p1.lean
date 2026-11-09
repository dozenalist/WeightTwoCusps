module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 432

The eta expression is `η(z)^2 η(2z)^(-1) η(48z)^2 η(72z)`; see
[the local level table](../../TABLE.md#level-432).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^2 η(2z)^(-1) η(48z)^2 η(72z)` at level 432. -/
abbrev cuspForm_432_eta_1p2_2m1_48p2_72p1 : gamma0CuspForms 432 :=
  etaQuotientCuspForm 432 sparse![432; 0 => 2, 1 => -1, 47 => 2, 71 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_432_eta_1p2_2m1_48p2_72p1_first_coeffs :
    first_coeffs 100 cuspForm_432_eta_1p2_2m1_48p2_72p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0, 2, 0, 0, 0, 0, -2, 0, 0, 0,
     0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0, 0, -4,
     0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, -1,
     6, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, -2, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
