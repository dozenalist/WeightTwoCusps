module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 56

The eta expression is `η(z) η(7z) η(8z) η(56z)`; see
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

/-- The cuspidal eta quotient `η(z) η(7z) η(8z) η(56z)` at level 56. -/
abbrev cuspForm_56_eta_1p1_7p1_8p1_56p1 : gamma0CuspForms 56 :=
  etaQuotientCuspForm 56 sparse![56; 0 => 1, 6 => 1, 7 => 1, 55 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_56_eta_1p1_7p1_8p1_56p1_first_coeffs :
    first_coeffs 100 cuspForm_56_eta_1p1_7p1_8p1_56p1 =
    [0, 0, 0, 1, -1, -1, 0, 0, 1, 0, 0, 0, 2, 1, 0, -2, -1, -2, 0, -1,
     0, 1, 0, 2, -2, 4, 0, -2, -1, 2, 0, 2, 1, 0, 0, -1, -1, -2, 0, -2,
     0, -2, 0, 0, 0, -1, 0, 2, 2, 0, 0, 2, 4, -4, 0, 0, 1, 0, 0, 3,
     0, -1, 0, 0, -1, 0, 0, -2, -6, 4, 0, 0, 1, -4, 0, 3, -2, 0, 0, -4,
     0, 0, 0, 3, 2, 2, 0, -2, 0, 4, 0, 1, 0, 0, 0, 2, -2, 2, 0, 0] := by
  eta_coeff

end WeightTwoCusps
