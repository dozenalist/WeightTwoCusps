module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 56

The eta expression is `η(2z)^(-1) η(4z)^3 η(14z)^3 η(28z)^(-1)`; see
[the local level table](../../TABLE.md#level-56).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-1) η(4z)^3 η(14z)^3 η(28z)^(-1)` at level 56. -/
abbrev cuspForm_56_eta_2m1_4p3_14p3_28m1 : gamma0CuspForms 56 :=
  etaQuotientCuspForm 56 sparse![56; 1 => -1, 3 => 3, 13 => 3, 27 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_56_eta_2m1_4p3_14p3_28m1_first_coeffs :
    first_coeffs 100 cuspForm_56_eta_2m1_4p3_14p3_28m1 =
    [0, 1, 0, 1, 0, -1, 0, 0, 0, -1, 0, -2, 0, 1, 0, -4, 0, -4, 0, 3,
     0, 1, 0, 4, 0, 5, 0, -2, 0, 4, 0, 6, 0, 0, 0, -3, 0, -4, 0, 0,
     0, 0, 0, 2, 0, -5, 0, -6, 0, 1, 0, -2, 0, -2, 0, -4, 0, -2, 0, 3,
     0, -1, 0, 2, 0, 2, 0, -8, 0, 8, 0, -4, 0, -2, 0, 11, 0, 2, 0, 4,
     0, -1, 0, 7, 0, -2, 0, 2, 0, 2, 0, -1, 0, 4, 0, 12, 0, -4, 0, 6] := by
  eta_coeff

end WeightTwoCusps
