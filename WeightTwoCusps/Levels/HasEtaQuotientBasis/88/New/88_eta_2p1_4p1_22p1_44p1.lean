module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 88

The eta expression is `η(2z) η(4z) η(22z) η(44z)`; see
[the local level table](../../TABLE.md#level-88).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(4z) η(22z) η(44z)` at level 88. -/
abbrev cuspForm_88_eta_2p1_4p1_22p1_44p1 : gamma0CuspForms 88 :=
  etaQuotientCuspForm 88 sparse![88; 1 => 1, 3 => 1, 21 => 1, 43 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_88_eta_2p1_4p1_22p1_44p1_first_coeffs :
    first_coeffs 100 cuspForm_88_eta_2p1_4p1_22p1_44p1 =
    [0, 0, 0, 1, 0, -1, 0, -2, 0, 1, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0,
     0, -2, 0, 1, 0, -3, 0, -1, 0, 2, 0, 1, 0, -1, 0, -2, 0, 1, 0, 0,
     0, 2, 0, 2, 0, 0, 0, 0, 0, 4, 0, 2, 0, -4, 0, 1, 0, -4, 0, -5,
     0, -2, 0, -4, 0, 4, 0, -1, 0, 5, 0, 3, 0, -2, 0, 0, 0, 2, 0, 2,
     0, 0, 0, 2, 0, -2, 0, 0, 0, -3, 0, 0, 0, -3, 0, 4, 0, -1, 0, -1] := by
  eta_coeff

end WeightTwoCusps
