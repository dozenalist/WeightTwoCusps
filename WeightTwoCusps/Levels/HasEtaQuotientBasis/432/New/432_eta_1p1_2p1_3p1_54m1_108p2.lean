module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 432

The eta expression is `η(z) η(2z) η(3z) η(54z)^(-1) η(108z)^2`; see
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

/-- The cuspidal eta quotient `η(z) η(2z) η(3z) η(54z)^(-1) η(108z)^2` at level 432. -/
abbrev cuspForm_432_eta_1p1_2p1_3p1_54m1_108p2 : gamma0CuspForms 432 :=
  etaQuotientCuspForm 432 sparse![432; 0 => 1, 1 => 1, 2 => 1, 53 => -1, 107 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_432_eta_1p1_2p1_3p1_54m1_108p2_first_coeffs :
    first_coeffs 100 cuspForm_432_eta_1p1_2p1_3p1_54m1_108p2 =
    [0, 0, 0, 0, 0, 0, 0, 1, -1, -2, 0, 1, 4, -1, 1, 0, -4, 1, -4, -1,
     -1, 4, 4, -2, 0, 4, 2, -2, 4, -3, -4, -4, -1, 0, 0, -1, 0, -3, 2, 4,
     0, 3, 0, 4, 1, 4, -4, 2, 0, -3, -1, 0, -8, -2, 4, 0, 1, -12, 4, 2,
     0, 1, -5, 0, 8, 2, 8, 3, 0, 0, -4, 0, 0, 3, -4, -4, 4, -3, 0, 7,
     3, -2, -4, -3, -16, -4, -2, 0, 0, 3, 8, -7, 2, 12, -4, 2, 0, 7, 3, 8] := by
  eta_coeff

end WeightTwoCusps
