module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 308

The eta expression is `η(4z) η(11z) η(28z) η(77z)`; see
[the local level table](../../TABLE.md#level-308).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z) η(11z) η(28z) η(77z)` at level 308. -/
abbrev cuspForm_308_eta_4p1_11p1_28p1_77p1 : gamma0CuspForms 308 :=
  etaQuotientCuspForm 308 sparse![308; 3 => 1, 10 => 1, 27 => 1, 76 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_308_eta_4p1_11p1_28p1_77p1_first_coeffs :
    first_coeffs 100 cuspForm_308_eta_4p1_11p1_28p1_77p1 =
    [0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0,
     1, 0, 0, 0, 1, 1, 0, -1, 0, 0, 0, 1, 0, 0, 0, 1, -1, 1, 0, 0,
     0, 1, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, -1, -2, 0, 0, 0, 0, 0, -1,
     1, -2, 0, -1, 1, 0, 0, 0, -1, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0,
     0, 0, 0, 2, 0, 0, 0, 0, 0, -1, 0, -1, 1, 3, 0, 0, 1, -1, 0, 0] := by
  eta_coeff

end WeightTwoCusps
