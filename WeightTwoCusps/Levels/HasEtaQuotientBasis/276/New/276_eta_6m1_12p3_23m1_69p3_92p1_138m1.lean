module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 276

The eta expression is `η(6z)^(-1) η(12z)^3 η(23z)^(-1) η(69z)^3 η(92z) η(138z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(6z)^(-1) η(12z)^3 η(23z)^(-1) η(69z)^3 η(92z) η(138z)^(-1)` at level 276. -/
abbrev cuspForm_276_eta_6m1_12p3_23m1_69p3_92p1_138m1 : gamma0CuspForms 276 :=
  etaQuotientCuspForm 276 sparse![276; 5 => -1, 11 => 3, 22 => -1, 68 => 3, 91 => 1, 137 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_276_eta_6m1_12p3_23m1_69p3_92p1_138m1_first_coeffs :
    first_coeffs 100 cuspForm_276_eta_6m1_12p3_23m1_69p3_92p1_138m1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 1, -2, 0, 0,
     0, 0, -1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 2, -1, -1, 0, 0, 0, 2,
     -2, 0, 0, 0, 0, -2, 1, 1, 0, 0, 0, 0, -1, 1, 0, 0, 0, -2, -1, -1,
     0, 0, 0, -4, 0, 1, 0, 0, 0, 2, 1, 0, 0, 0, 0, -2, 1, 2, 0, 1] := by
  eta_coeff

end WeightTwoCusps
