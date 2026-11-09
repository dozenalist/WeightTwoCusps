module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 308

The eta expression is `η(z) η(2z) η(4z)^(-1) η(11z)^(-1) η(14z)^(-1) η(22z) η(28z)^2 η(44z) η(77z)^2 η(154z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z) η(2z) η(4z)^(-1) η(11z)^(-1) η(14z)^(-1) η(22z) η(28z)^2 η(44z) η(77z)^2 η(154z)^(-1)` at level 308. -/
abbrev cuspForm_308_eta_1p1_2p1_4m1_11m1_14m1_22p1_28p2_44p1_77p2_154m1 : gamma0CuspForms 308 :=
  etaQuotientCuspForm 308 sparse![308; 0 => 1, 1 => 1, 3 => -1, 10 => -1, 13 => -1, 21 => 1, 27 => 2, 43 => 1, 76 => 2, 153 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_308_eta_1p1_2p1_4m1_11m1_14m1_22p1_28p2_44p1_77p2_154m1_first_coeffs :
    first_coeffs 100 cuspForm_308_eta_1p1_2p1_4m1_11m1_14m1_22p1_28p2_44p1_77p2_154m1 =
    [0, 0, 0, 0, 1, -1, -2, 1, 1, 1, -1, 1, 2, -2, -2, 1, 0, -3, 1, 0,
     2, -1, -1, 5, 0, -1, 1, -1, -2, -1, -3, 3, 0, -2, 4, 1, 1, 1, -5, -3,
     3, -2, 2, 0, 1, 5, -4, 0, 1, -2, -2, 2, -2, -1, -2, 0, 8, 0, 1, 2,
     -1, -5, -1, -2, 2, -3, 2, 6, -1, 0, -2, -1, -6, 6, -2, 1, -1, 1, 7, -5,
     -1, -3, 4, 0, 2, -7, -4, 1, -1, 8, 3, 4, -1, -1, -3, 3, -6, -2, 4, 1] := by
  eta_coeff

end WeightTwoCusps
