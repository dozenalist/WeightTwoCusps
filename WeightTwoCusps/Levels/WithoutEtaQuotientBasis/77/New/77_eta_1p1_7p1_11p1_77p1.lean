module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 77

The eta expression is `η(z) η(7z) η(11z) η(77z)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-77).
The table has full eta basis = NO at this level: these supporting forms
do not span the whole cusp-form space.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(7z) η(11z) η(77z)` at level 77. -/
abbrev cuspForm_77_eta_1p1_7p1_11p1_77p1 : gamma0CuspForms 77 :=
  etaQuotientCuspForm 77 sparse![77; 0 => 1, 6 => 1, 10 => 1, 76 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_77_eta_1p1_7p1_11p1_77p1_first_coeffs :
    first_coeffs 100 cuspForm_77_eta_1p1_7p1_11p1_77p1 =
    [0, 0, 0, 0, 1, -1, -1, 0, 0, 1, 0, 0, 1, 1, 0, -1, -1, 1, -2, 0,
     0, 0, 0, -1, -1, -1, 1, 3, 1, 2, 2, -2, 0, 0, -1, -1, 1, -3, 2, 0,
     0, -3, -1, 0, -1, 0, 2, 1, -1, 0, 0, 2, -1, 2, -2, 1, 0, -2, 2, 2,
     0, 1, 1, 1, -1, 2, 1, 1, -3, -3, 0, -3, -2, -1, -2, -1, 2, 0, 0, 2,
     -2, 2, -1, -2, 1, 4, 0, 0, 0, 1, 4, 1, 0, -3, -1, -2, 3, 1, 0, -1] := by
  eta_coeff

end WeightTwoCusps
