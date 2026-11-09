module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 405

The eta expression is `η(z) η(5z) η(15z) η(27z)`; see
[the local level table](../../TABLE.md#level-405).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(5z) η(15z) η(27z)` at level 405. -/
abbrev cuspForm_405_eta_1p1_5p1_15p1_27p1 : gamma0CuspForms 405 :=
  etaQuotientCuspForm 405 sparse![405; 0 => 1, 4 => 1, 14 => 1, 26 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_405_eta_1p1_5p1_15p1_27p1_first_coeffs :
    first_coeffs 100 cuspForm_405_eta_1p1_5p1_15p1_27p1 =
    [0, 0, 1, -1, -1, 0, 0, 0, 1, 2, 0, 0, -2, 1, -1, 0, 0, -3, 1, 1,
     0, 0, 1, -1, 0, 0, 0, 4, -1, -2, 1, 1, 2, 0, 1, -1, -2, -1, -3, -4,
     -1, 1, 0, -1, 7, -1, -1, 3, 1, -1, 1, 0, -1, 4, -4, 1, 0, -1, 0, 1,
     0, -1, -6, 0, 1, 3, 8, -3, 1, 0, 1, -1, -3, 0, -5, -1, -1, 2, 0, 0,
     -4, -4, 3, 0, 6, 1, -5, 0, 1, 3, -2, 1, 4, 3, 4, 0, 0, 4, -4, 4] := by
  eta_coeff

end WeightTwoCusps
