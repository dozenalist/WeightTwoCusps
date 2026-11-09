module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 308

The eta expression is `η(z)^2 η(2z)^(-2) η(4z)^2 η(7z)^(-1) η(14z)^2 η(28z)^(-1) η(77z) η(308z)`; see
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

/-- The cuspidal eta quotient `η(z)^2 η(2z)^(-2) η(4z)^2 η(7z)^(-1) η(14z)^2 η(28z)^(-1) η(77z) η(308z)` at level 308. -/
abbrev cuspForm_308_eta_1p2_2m2_4p2_7m1_14p2_28m1_77p1_308p1 : gamma0CuspForms 308 :=
  etaQuotientCuspForm 308 sparse![308; 0 => 2, 1 => -2, 3 => 2, 6 => -1, 13 => 2, 27 => -1, 76 => 1, 307 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_308_eta_1p2_2m2_4p2_7m1_14p2_28m1_77p1_308p1_first_coeffs :
    first_coeffs 100 cuspForm_308_eta_1p2_2m2_4p2_7m1_14p2_28m1_77p1_308p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 1, -2,
     2, 0, 3, -1, -2, -1, 0, 0, 1, 1, -2, -2, 2, 2, 0, 1, -1, -3, -2, 5,
     0, 2, 0, 2, -3, -2, 0, -2, -2, 1, 1, 1, -2, 2, -2, 0, 1, 4, -2, 0,
     1, 2, 2, 1, 2, -2, -6, 0, -4, 4, 1, 0, -1, -4, 1, -2, 2, -1, 1, 2,
     -4, 1, 2, 2, 0, 3, -1, -4, 2, 0, 2, 2, 4, -3, -2, 3, 0, -4, 0, -1] := by
  eta_coeff

end WeightTwoCusps
