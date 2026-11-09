module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 432

The eta expression is `η(z) η(2z) η(3z) η(6z)^(-1) η(36z)^2`; see
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

/-- The cuspidal eta quotient `η(z) η(2z) η(3z) η(6z)^(-1) η(36z)^2` at level 432. -/
abbrev cuspForm_432_eta_1p1_2p1_3p1_6m1_36p2 : gamma0CuspForms 432 :=
  etaQuotientCuspForm 432 sparse![432; 0 => 1, 1 => 1, 2 => 1, 5 => -1, 35 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_432_eta_1p1_2p1_3p1_6m1_36p2_first_coeffs :
    first_coeffs 100 cuspForm_432_eta_1p1_2p1_3p1_6m1_36p2 =
    [0, 0, 0, 1, -1, -2, 0, 1, 4, 0, 0, -2, -4, 2, 0, 0, -2, 0, 0, 1,
     4, 4, 0, -4, 0, 0, 0, 0, -3, -4, 0, 0, 4, 0, 0, -2, 0, 2, 0, 2,
     0, 4, 0, 0, -4, 0, 0, 4, 0, -4, 0, 0, 3, -6, 0, 0, -4, -8, 0, 8,
     0, 2, 0, 0, 4, 8, 0, 1, 0, 0, 0, 0, 0, -4, 0, -5, 3, -2, 0, -5,
     -12, 0, 0, -2, 16, 0, 0, 0, 0, 12, 0, -5, -8, 4, 0, 4, 0, -4, 0, 0] := by
  eta_coeff

end WeightTwoCusps
