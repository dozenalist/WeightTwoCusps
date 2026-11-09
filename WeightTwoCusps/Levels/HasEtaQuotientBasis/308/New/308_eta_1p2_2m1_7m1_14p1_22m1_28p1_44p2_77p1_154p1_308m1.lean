module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 308

The eta expression is `η(z)^2 η(2z)^(-1) η(7z)^(-1) η(14z) η(22z)^(-1) η(28z) η(44z)^2 η(77z) η(154z) η(308z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^2 η(2z)^(-1) η(7z)^(-1) η(14z) η(22z)^(-1) η(28z) η(44z)^2 η(77z) η(154z) η(308z)^(-1)` at level 308. -/
abbrev cuspForm_308_eta_1p2_2m1_7m1_14p1_22m1_28p1_44p2_77p1_154p1_308m1 : gamma0CuspForms 308 :=
  etaQuotientCuspForm 308 sparse![308; 0 => 2, 1 => -1, 6 => -1, 13 => 1, 21 => -1, 27 => 1, 43 => 2, 76 => 1, 153 => 1, 307 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_308_eta_1p2_2m1_7m1_14p1_22m1_28p1_44p2_77p1_154p1_308m1_first_coeffs :
    first_coeffs 100 cuspForm_308_eta_1p2_2m1_7m1_14p1_22m1_28p1_44p2_77p1_154p1_308m1 =
    [0, 1, -2, 0, 0, 2, 0, 0, 1, -2, -2, 0, 2, 0, 0, 1, -2, 0, 0, 2,
     0, 0, 2, -3, -2, 0, 2, 2, 0, 1, -1, -4, -2, 0, 2, 0, 2, -1, 0, 0,
     2, 2, 0, 3, -2, -6, 0, 2, 2, 0, 1, -3, -4, -2, 4, 0, 0, 1, 0, -2,
     2, 2, 2, 0, 2, -1, -4, -1, 0, 2, 0, 3, -3, -6, -1, 2, 2, 0, 4, 1,
     -4, 1, -2, 2, 0, 4, 0, -2, 2, -2, 2, 0, 2, -3, -8, -1, -2, 2, 0, 0] := by
  eta_coeff

end WeightTwoCusps
