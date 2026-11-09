module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 150

The eta expression is `η(5z) η(6z) η(10z) η(75z)`; see
[the local level table](../../TABLE.md#level-150).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(5z) η(6z) η(10z) η(75z)` at level 150. -/
abbrev cuspForm_150_eta_5p1_6p1_10p1_75p1 : gamma0CuspForms 150 :=
  etaQuotientCuspForm 150 sparse![150; 4 => 1, 5 => 1, 9 => 1, 74 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_150_eta_5p1_6p1_10p1_75p1_first_coeffs :
    first_coeffs 100 cuspForm_150_eta_5p1_6p1_10p1_75p1 =
    [0, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1, 0, 0, 0, -2, 1, -1, 0, 0, 1,
     2, 1, 0, 0, 0, -1, 2, 0, 0, 2, 0, -1, 0, 0, 2, -2, 0, 0, 0, -1,
     -1, -2, 0, 0, -2, 0, 0, 0, 0, -1, 0, -1, 0, 0, 1, 2, -2, 0, 0, 0,
     -1, 3, 0, 0, -1, 2, -1, 0, 0, 0, 2, 4, 0, 0, 2, 0, 2, 0, 0, -4,
     -2, 1, 0, 0, 2, 2, 0, 0, 0, 2, -1, -1, 0, 0, -4, -4, 0, 0, 0, 3] := by
  eta_coeff

end WeightTwoCusps
