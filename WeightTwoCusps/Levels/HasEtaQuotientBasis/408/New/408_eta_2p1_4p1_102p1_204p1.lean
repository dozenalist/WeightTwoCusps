module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 408

The eta expression is `η(2z) η(4z) η(102z) η(204z)`; see
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

/-- The cuspidal eta quotient `η(2z) η(4z) η(102z) η(204z)` at level 408. -/
abbrev cuspForm_408_eta_2p1_4p1_102p1_204p1 : gamma0CuspForms 408 :=
  etaQuotientCuspForm 408 sparse![408; 1 => 1, 3 => 1, 101 => 1, 203 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_408_eta_2p1_4p1_102p1_204p1_first_coeffs :
    first_coeffs 100 cuspForm_408_eta_2p1_4p1_102p1_204p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, -2, 0, 1,
     0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, -2, 0, 1, 0, -2, 0, -2, 0, 0,
     0, 2, 0, -1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0,
     0, -2, 0, 0, 0, 0, 0, 0, 0, -1, 0, -2, 0, -2, 0, 0, 0, 2, 0, 0,
     0, 0, 0, -2, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0] := by
  eta_coeff

end WeightTwoCusps
