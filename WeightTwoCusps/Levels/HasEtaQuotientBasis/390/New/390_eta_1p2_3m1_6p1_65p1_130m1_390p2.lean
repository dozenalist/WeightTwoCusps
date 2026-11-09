module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 390

The eta expression is `η(z)^2 η(3z)^(-1) η(6z) η(65z) η(130z)^(-1) η(390z)^2`; see
[the local level table](../../TABLE.md#level-390).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^2 η(3z)^(-1) η(6z) η(65z) η(130z)^(-1) η(390z)^2` at level 390. -/
abbrev cuspForm_390_eta_1p2_3m1_6p1_65p1_130m1_390p2 : gamma0CuspForms 390 :=
  etaQuotientCuspForm 390 sparse![390; 0 => 2, 2 => -1, 5 => 1, 64 => 1, 129 => -1, 389 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_390_eta_1p2_3m1_6p1_65p1_130m1_390p2_first_coeffs :
    first_coeffs 100 cuspForm_390_eta_1p2_3m1_6p1_65p1_130m1_390p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, -1, 3, -1, 1, 1, -1, -1, 0,
     -2, -2, 2, 1, 3, -1, 1, 0, 0, -1, -1, 1, 0, -1, -3, 2, 0, -1, -2, 1,
     0, 3, 2, -1, 2, 1, 0, 0, -3, -1, 1, 0, -2, 0, 1, -3, 1, 0, 0, -1,
     2, -1, 3, -2, -2, 0, 0, 2, 3, 4, -1, 0, -2, 0, 0, -2, 2, 2, -4, -2] := by
  eta_coeff

end WeightTwoCusps
