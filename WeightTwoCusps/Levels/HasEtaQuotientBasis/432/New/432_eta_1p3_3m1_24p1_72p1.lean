module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 432

The eta expression is `η(z)^3 η(3z)^(-1) η(24z) η(72z)`; see
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

/-- The cuspidal eta quotient `η(z)^3 η(3z)^(-1) η(24z) η(72z)` at level 432. -/
abbrev cuspForm_432_eta_1p3_3m1_24p1_72p1 : gamma0CuspForms 432 :=
  etaQuotientCuspForm 432 sparse![432; 0 => 3, 2 => -1, 23 => 1, 71 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_432_eta_1p3_3m1_24p1_72p1_first_coeffs :
    first_coeffs 100 cuspForm_432_eta_1p3_3m1_24p1_72p1 =
    [0, 0, 0, 0, 1, -3, 0, 6, -3, 0, 0, -6, 0, 6, 0, 0, 6, -6, 0, 0,
     -3, 0, 0, -6, 0, 12, 0, 0, -1, 0, 0, 0, -3, 0, 0, 0, 0, -6, 0, 0,
     0, 0, 0, 12, 3, 0, 0, 0, 0, -12, 0, 0, 5, -3, 0, -12, 3, 0, 0, 12,
     0, 6, 0, 0, -12, 6, 0, 0, 0, 0, 0, 6, 0, -12, 0, 0, -7, 9, 0, -6,
     9, 0, 0, 6, 0, -12, 0, 0, 0, 18, 0, -24, 6, 0, 0, 6, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
