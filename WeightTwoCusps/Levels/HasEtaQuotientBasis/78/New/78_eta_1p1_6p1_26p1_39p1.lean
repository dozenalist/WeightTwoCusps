module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 78

The eta expression is `η(z) η(6z) η(26z) η(39z)`; see
[the local level table](../../TABLE.md#level-78).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(6z) η(26z) η(39z)` at level 78. -/
abbrev cuspForm_78_eta_1p1_6p1_26p1_39p1 : gamma0CuspForms 78 :=
  etaQuotientCuspForm 78 sparse![78; 0 => 1, 5 => 1, 25 => 1, 38 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_78_eta_1p1_6p1_26p1_39p1_first_coeffs :
    first_coeffs 100 cuspForm_78_eta_1p1_6p1_26p1_39p1 =
    [0, 0, 0, 1, -1, -1, 0, 0, 1, -1, 2, 1, 0, 0, -1, -2, 0, 1, -1, 0,
     -1, 1, -1, 0, 1, 1, 0, 1, 0, 0, 2, 0, 0, 1, -2, -1, -2, -2, 0, 0,
     2, 1, -1, -1, 3, 0, 0, -3, 1, -1, 0, -1, 1, 0, 3, 0, -1, 2, 0, 1,
     -2, 4, -2, -1, -1, 0, -3, 4, -1, -2, 0, 1, 0, 0, 3, 0, 0, 0, -1, -2,
     -5, -4, 1, 1, 1, -2, 4, 4, -3, -1, 3, -1, 4, 0, 2, 2, 0, -2, 2, 3] := by
  eta_coeff

end WeightTwoCusps
