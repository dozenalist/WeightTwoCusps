module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 276

The eta expression is `η(3z)^3 η(6z)^(-1) η(23z) η(92z)^(-1) η(138z)^(-1) η(276z)^3`; see
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

/-- The cuspidal eta quotient `η(3z)^3 η(6z)^(-1) η(23z) η(92z)^(-1) η(138z)^(-1) η(276z)^3` at level 276. -/
abbrev cuspForm_276_eta_3p3_6m1_23p1_92m1_138m1_276p3 : gamma0CuspForms 276 :=
  etaQuotientCuspForm 276 sparse![276; 2 => 3, 5 => -1, 22 => 1, 91 => -1, 137 => -1, 275 => 3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_276_eta_3p3_6m1_23p1_92m1_138m1_276p3_first_coeffs :
    first_coeffs 100 cuspForm_276_eta_3p3_6m1_23p1_92m1_138m1_276p3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 1, 0, 0, -3, 0, 0, 1, 0, 0, 2, 0, 0, 2, 0,
     0, -1, 0, 0, -4, 0, 0, 1, 0, -1, -2, 0, 3, 0, 0, -1, 2, 0, -2, 4,
     0, -2, -1, 0, 1, 2, 0, 4, -2, 0, -1, -1, -1, 2, 0, 3, 0, -2, -1, -2,
     -2, -2, -4, -2, -2, 1, 0, 1, -2, 4, 4, 2, 1, -1, 1, 0, 2, 0, 2, 0] := by
  eta_coeff

end WeightTwoCusps
