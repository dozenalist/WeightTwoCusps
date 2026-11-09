module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-1) η(2z)^(-1) η(3z)^2 η(4z)^5 η(6z)^(-1) η(8z)^(-2) η(11z) η(132z)^(-1) η(264z)^2`; see
[the local level table](../../TABLE.md#level-264).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^(-1) η(3z)^2 η(4z)^5 η(6z)^(-1) η(8z)^(-2) η(11z) η(132z)^(-1) η(264z)^2` at level 264. -/
abbrev cuspForm_264_eta_1m1_2m1_3p2_4p5_6m1_8m2_11p1_132m1_264p2 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -1, 1 => -1, 2 => 2, 3 => 5, 5 => -1, 7 => -2, 10 => 1, 131 => -1, 263 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m1_2m1_3p2_4p5_6m1_8m2_11p1_132m1_264p2_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m1_2m1_3p2_4p5_6m1_8m2_11p1_132m1_264p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 3,
     2, 2, 1, 0, 3, 2, 4, 2, -1, 0, -1, 0, 1, -1, 2, -1, 0, 0, -2, 0,
     2, -3, -2, -4, -1, 0, -5, 0, -8, 0, 3, -1, -3, -4, 0, 0, -2, 1, -6, -2,
     0, -1, -8, -3, 0, -3, 0, -2, 0, -2, 2, -2, -5, -3, 5, 4, 0, 1, -4, -1,
     0, -2, 2, -6, 3, -1, -2, -2, 0, 8, -1, 2, 2, -4, 3, 5, 6, -2, -2, 1] := by
  eta_coeff

end WeightTwoCusps
