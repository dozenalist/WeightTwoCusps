module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 150

The eta expression is `η(z) η(15z) η(30z) η(50z)`; see
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

/-- The cuspidal eta quotient `η(z) η(15z) η(30z) η(50z)` at level 150. -/
abbrev cuspForm_150_eta_1p1_15p1_30p1_50p1 : gamma0CuspForms 150 :=
  etaQuotientCuspForm 150 sparse![150; 0 => 1, 14 => 1, 29 => 1, 49 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_150_eta_1p1_15p1_30p1_50p1_first_coeffs :
    first_coeffs 100 cuspForm_150_eta_1p1_15p1_30p1_50p1 =
    [0, 0, 0, 0, 1, -1, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, -1, 0, 0, -2,
     1, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1, 1, 0, 0, -1, 2, 2, 0, 0, -3,
     0, -3, 0, 0, -1, -1, 2, 0, 0, 3, -1, -1, 0, 0, 1, 2, 0, 0, 0, 0,
     -2, -1, 0, 0, -1, 0, 1, 0, 0, 4, -2, 0, 0, 0, 2, 1, -1, 0, 0, 2,
     -3, -4, 0, 0, 2, -4, 0, 0, 0, 3, 0, -1, 0, 0, 0, 0, -1, 0, 0, -2] := by
  eta_coeff

end WeightTwoCusps
