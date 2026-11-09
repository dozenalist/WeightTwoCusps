module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 276

The eta expression is `η(z) η(12z) η(23z) η(276z)`; see
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

/-- The cuspidal eta quotient `η(z) η(12z) η(23z) η(276z)` at level 276. -/
abbrev cuspForm_276_eta_1p1_12p1_23p1_276p1 : gamma0CuspForms 276 :=
  etaQuotientCuspForm 276 sparse![276; 0 => 1, 11 => 1, 22 => 1, 275 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_276_eta_1p1_12p1_23p1_276p1_first_coeffs :
    first_coeffs 100 cuspForm_276_eta_1p1_12p1_23p1_276p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 0, 0, 1, 0,
     1, 0, 0, 0, 0, -2, 1, 1, -1, 0, -1, 0, -1, 0, 0, 1, -1, 1, 2, 2,
     1, -1, -1, -1, -1, 0, 0, -1, 1, 0, -1, 0, 1, 0, 0, 1, 0, 0, -1, -2,
     2, 0, -2, -2, 0, 2, -1, 1, 0, 0, 2, 3, -1, 0, 1, -2, 1, 1, 2, 0,
     1, -1, 0, -2, -1, -3, 0, -1, -2, 0, 0, 0, 0, 0, 0, 0, -1, 3, -1, 2] := by
  eta_coeff

end WeightTwoCusps
