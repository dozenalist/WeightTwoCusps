module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 390

The eta expression is `η(6z) η(10z) η(39z) η(65z)`; see
[the local level table](../../TABLE.md#level-390).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z) η(10z) η(39z) η(65z)` at level 390. -/
abbrev cuspForm_390_eta_6p1_10p1_39p1_65p1 : gamma0CuspForms 390 :=
  etaQuotientCuspForm 390 sparse![390; 5 => 1, 9 => 1, 38 => 1, 64 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_390_eta_6p1_10p1_39p1_65p1_first_coeffs :
    first_coeffs 100 cuspForm_390_eta_6p1_10p1_39p1_65p1 =
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, -1, 0, 0,
     0, 1, 0, 0, 0, -1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0,
     0, 0, 0, 0, -1, -1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, -1, 0, 0,
     -1, -1, 0, 0, 1, 0, -1, -2, 0, 0, -2, 0, 0, 0, -1, 1, 0, -1, 0, 0,
     1, -1, 1, -1, 1, 1, -2, 0, 0, 1, 1, 0, -1, 1, 0, 0, 0, 2, 0, -1] := by
  eta_coeff

end WeightTwoCusps
