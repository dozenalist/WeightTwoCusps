module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 390

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^3 η(6z)^(-2) η(65z) η(390z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^3 η(6z)^(-2) η(65z) η(390z)` at level 390. -/
abbrev cuspForm_390_eta_1m2_2p3_3p3_6m2_65p1_390p1 : gamma0CuspForms 390 :=
  etaQuotientCuspForm 390 sparse![390; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 64 => 1, 389 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_390_eta_1m2_2p3_3p3_6m2_65p1_390p1_first_coeffs :
    first_coeffs 100 cuspForm_390_eta_1m2_2p3_3p3_6m2_65p1_390p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
     2, 2, 1, -1, 0, 0, 1, 1, -3, -2, -3, 1, 1, -2, 1, -3, -1, -1, -1, 0,
     -3, 1, 0, -2, 1, 1, 2, -1, 0, 0, -3, 1, 0, 0, -1, 3, 3, 1, -1, 2,
     3, -1, 2, -3, 0, 0, 1, 2, -1, 1, 4, 1, 0, 1, -1, 0, 1, 3, 0, -1,
     0, 2, 0, 0, -1, -5, -3, -1, 0, 1, 3, -1, -2, 2, 3, 5, 0, 0, -1, -1] := by
  eta_coeff

end WeightTwoCusps
