module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 408

The eta expression is `η(12z)^2 η(34z)^(-2) η(68z)^4 η(102z)^2 η(204z)^(-2)`; see
[the local level table](../../TABLE.md#level-408).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(12z)^2 η(34z)^(-2) η(68z)^4 η(102z)^2 η(204z)^(-2)` at level 408. -/
abbrev cuspForm_408_eta_12p2_34m2_68p4_102p2_204m2 : gamma0CuspForms 408 :=
  etaQuotientCuspForm 408 sparse![408; 11 => 2, 33 => -2, 67 => 4, 101 => 2, 203 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_408_eta_12p2_34m2_68p4_102p2_204m2_first_coeffs :
    first_coeffs 100 cuspForm_408_eta_12p2_34m2_68p4_102p2_204m2 =
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0,
     0, 0, 0, 0, 0, 0, 0, -4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2,
     0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 0, -2, 0, 0, 0, 0, 0, 0,
     0, -2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 4, 0, -2, 0, 0] := by
  eta_coeff

end WeightTwoCusps
