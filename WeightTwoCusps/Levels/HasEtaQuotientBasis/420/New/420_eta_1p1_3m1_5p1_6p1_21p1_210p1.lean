module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(z) η(3z)^(-1) η(5z) η(6z) η(21z) η(210z)`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(3z)^(-1) η(5z) η(6z) η(21z) η(210z)` at level 420. -/
abbrev cuspForm_420_eta_1p1_3m1_5p1_6p1_21p1_210p1 : gamma0CuspForms 420 :=
  etaQuotientCuspForm 420 sparse![420; 0 => 1, 2 => -1, 4 => 1, 5 => 1, 20 => 1, 209 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_420_eta_1p1_3m1_5p1_6p1_21p1_210p1_first_coeffs :
    first_coeffs 100 cuspForm_420_eta_1p1_3m1_5p1_6p1_21p1_210p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 1, -1, -1, 2, 1, -1, 3,
     -2, -1, 2, -2, -1, 2, -1, -2, 3, -4, -1, 3, 0, -1, 3, 1, -1, 2, -3, -1,
     2, -1, -2, 4, 1, -2, 2, -3, -1, 3, 0, -2, 1, 0, -1, 2, -5, -1, 2, -3,
     -1, 2, 2, 0, 2, -3, -1, 4, -1, 0, 3, 5, -1, 1, -4, -1, 3, -1, -1, 0,
     0, -1, 1, -4, -1, 0, -1, 0, 2, 3, -1, -2, -4, -2, 2, -1, 0, 1, 5, 0] := by
  eta_coeff

end WeightTwoCusps
