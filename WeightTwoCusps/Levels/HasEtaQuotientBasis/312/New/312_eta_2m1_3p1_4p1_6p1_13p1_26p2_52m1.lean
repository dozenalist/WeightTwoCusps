module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 312

The eta expression is `η(2z)^(-1) η(3z) η(4z) η(6z) η(13z) η(26z)^2 η(52z)^(-1)`; see
[the local level table](../../TABLE.md#level-312).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-1) η(3z) η(4z) η(6z) η(13z) η(26z)^2 η(52z)^(-1)` at level 312. -/
abbrev cuspForm_312_eta_2m1_3p1_4p1_6p1_13p1_26p2_52m1 : gamma0CuspForms 312 :=
  etaQuotientCuspForm 312 sparse![312; 1 => -1, 2 => 1, 3 => 1, 5 => 1, 12 => 1, 25 => 2, 51 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_312_eta_2m1_3p1_4p1_6p1_13p1_26p2_52m1_first_coeffs :
    first_coeffs 100 cuspForm_312_eta_2m1_3p1_4p1_6p1_13p1_26p2_52m1 =
    [0, 1, 0, 1, -1, 1, -1, 0, -1, 0, -1, 1, -1, 0, -3, 1, -1, 1, -2, 2,
     -1, 2, 0, 2, -2, 2, 0, -1, -2, -2, 3, 0, 2, 3, 0, 1, 2, -2, 2, 0,
     7, -1, 1, -1, 3, -3, 0, -3, -3, -4, 4, -5, 0, 0, 3, 0, -5, -6, -2, -7,
     5, 0, -2, 2, -1, 0, -2, -2, 1, -2, 2, -3, 5, -2, 5, 0, 0, 2, -1, -6,
     3, 1, 8, 5, 2, 2, 0, -2, 4, -3, 2, 1, 2, 0, 3, 0, 3, 0, -2, -1] := by
  eta_coeff

end WeightTwoCusps
