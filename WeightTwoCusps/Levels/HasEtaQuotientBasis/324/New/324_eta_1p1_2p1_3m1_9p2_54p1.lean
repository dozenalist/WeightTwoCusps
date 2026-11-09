module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 324

The eta expression is `η(z) η(2z) η(3z)^(-1) η(9z)^2 η(54z)`; see
[the local level table](../../TABLE.md#level-324).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(2z) η(3z)^(-1) η(9z)^2 η(54z)` at level 324. -/
abbrev cuspForm_324_eta_1p1_2p1_3m1_9p2_54p1 : gamma0CuspForms 324 :=
  etaQuotientCuspForm 324 sparse![324; 0 => 1, 1 => 1, 2 => -1, 8 => 2, 53 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_324_eta_1p1_2p1_3m1_9p2_54p1_first_coeffs :
    first_coeffs 100 cuspForm_324_eta_1p1_2p1_3m1_9p2_54p1 =
    [0, 0, 0, 1, -1, -2, 2, -1, 0, 4, -2, -2, 2, 0, 0, 2, -2, -4, 0, -1,
     0, 3, -1, 2, 2, 1, 0, 0, 1, -2, 0, -2, 0, -2, 0, 2, 0, 1, 0, -3,
     1, -2, -2, 1, 0, 0, 1, 6, -4, 2, 0, 0, 1, 4, 0, -1, 0, -3, 5, 2,
     -6, 1, 0, -16, 3, 2, 0, 1, 0, -4, 5, 8, 0, 3, 0, -5, 1, 2, -8, -3,
     0, 0, 1, 6, -2, 3, 0, 4, 5, -4, 0, 1, 0, -4, -4, 8, 2, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
