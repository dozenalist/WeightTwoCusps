module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 276

The eta expression is `η(z)^(-1) η(3z) η(4z)^3 η(12z)^(-1) η(23z)^2`; see
[the local level table](../../TABLE.md#level-276).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(3z) η(4z)^3 η(12z)^(-1) η(23z)^2` at level 276. -/
abbrev cuspForm_276_eta_1m1_3p1_4p3_12m1_23p2 : gamma0CuspForms 276 :=
  etaQuotientCuspForm 276 sparse![276; 0 => -1, 2 => 1, 3 => 3, 11 => -1, 22 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_276_eta_1m1_3p1_4p3_12m1_23p2_first_coeffs :
    first_coeffs 100 cuspForm_276_eta_1m1_3p1_4p3_12m1_23p2 =
    [0, 0, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 1, 0, 3, 2, 3, 1, 2, 3,
     0, 1, 1, 0, 3, -1, 0, -4, -2, 3, -3, 0, -5, 0, -2, 0, 1, -5, -2, -3,
     -1, -4, -4, 3, 1, -2, 1, -5, -3, -2, 0, -6, -9, -2, -1, -4, -5, 1, -3, 1,
     -2, -5, -9, -2, 1, -6, -4, -7, 1, -2, -5, 2, -4, 2, 5, -5, -1, -5, 3, 4,
     0, 0, -6, -1, 3, 5, 0, 0, 3, -7, -1, 0, -1, 6, 7, -1, -3, 0, 6, 5] := by
  eta_coeff

end WeightTwoCusps
