module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 308

The eta expression is `η(2z)^2 η(4z)^(-1) η(11z) η(14z)^2 η(22z)^(-1) η(28z)^(-1) η(44z) η(77z) η(154z)^(-1) η(308z)`; see
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

/-- The cuspidal eta quotient `η(2z)^2 η(4z)^(-1) η(11z) η(14z)^2 η(22z)^(-1) η(28z)^(-1) η(44z) η(77z) η(154z)^(-1) η(308z)` at level 308. -/
abbrev cuspForm_308_eta_2p2_4m1_11p1_14p2_22m1_28m1_44p1_77p1_154m1_308p1 : gamma0CuspForms 308 :=
  etaQuotientCuspForm 308 sparse![308; 1 => 2, 3 => -1, 10 => 1, 13 => 2, 21 => -1, 27 => -1, 43 => 1, 76 => 1, 153 => -1, 307 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_308_eta_2p2_4m1_11p1_14p2_22m1_28m1_44p1_77p1_154m1_308p1_first_coeffs :
    first_coeffs 100 cuspForm_308_eta_2p2_4m1_11p1_14p2_22m1_28m1_44p1_77p1_154m1_308p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -2, 0, 0, 0, 0, 0, 2,
     0, 0, -1, 0, 2, -2, 0, 4, 0, -2, -2, 0, 0, -4, 0, 0, 2, 0, -4, 0,
     2, 0, 0, 6, 3, 0, 2, 0, 0, 0, 0, 0, -2, 0, -6, 0, 0, -4, 2, 0,
     -4, -2, 2, 0, 0, 0, 4, 2, 4, -4, 0, 0, 2, 0, 0, 8, -6, 1, -2, -2,
     4, 0, 0, 2, 0, -2, -8, 0, -1, 0, 6, -2, 0, 4, 0, -2, 2, -4, 0, 1] := by
  eta_coeff

end WeightTwoCusps
