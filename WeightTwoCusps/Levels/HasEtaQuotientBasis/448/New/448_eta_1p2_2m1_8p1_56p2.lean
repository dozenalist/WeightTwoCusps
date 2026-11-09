module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 448

The eta expression is `η(z)^2 η(2z)^(-1) η(8z) η(56z)^2`; see
[the local level table](../../TABLE.md#level-448).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^2 η(2z)^(-1) η(8z) η(56z)^2` at level 448. -/
abbrev cuspForm_448_eta_1p2_2m1_8p1_56p2 : gamma0CuspForms 448 :=
  etaQuotientCuspForm 448 sparse![448; 0 => 2, 1 => -1, 7 => 1, 55 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_448_eta_1p2_2m1_8p1_56p2_first_coeffs :
    first_coeffs 100 cuspForm_448_eta_1p2_2m1_8p1_56p2 =
    [0, 0, 0, 0, 0, 1, -2, 0, 0, 2, 0, 0, 0, -1, 0, 0, 0, -2, 0, 0,
     0, 1, 4, 0, 0, -2, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, -2, 2, 0,
     0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, -2, 0, 0,
     0, 1, 4, 0, 0, -2, 0, 0, 0, 4, -2, 0, 0, 4, 0, 0, 0, -2, -8, 0,
     0, 6, 0, 0, 0, 2, -4, 0, 0, 0, 0, 0, 0, 4, -4, 0, 0, -2, 0, 0] := by
  eta_coeff

end WeightTwoCusps
