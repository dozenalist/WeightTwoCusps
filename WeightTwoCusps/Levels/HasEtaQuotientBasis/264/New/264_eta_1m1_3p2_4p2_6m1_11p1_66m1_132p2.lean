module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-1) η(3z)^2 η(4z)^2 η(6z)^(-1) η(11z) η(66z)^(-1) η(132z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^2 η(4z)^2 η(6z)^(-1) η(11z) η(66z)^(-1) η(132z)^2` at level 264. -/
abbrev cuspForm_264_eta_1m1_3p2_4p2_6m1_11p1_66m1_132p2 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -1, 2 => 2, 3 => 2, 5 => -1, 10 => 1, 65 => -1, 131 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m1_3p2_4p2_6m1_11p1_66m1_132p2_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m1_3p2_4p2_6m1_11p1_66m1_132p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 0,
     0, 1, 0, 1, 0, -1, 1, -2, 0, 0, 2, 0, -3, -2, -2, -1, 1, -1, -4, -1,
     -1, 1, -3, -1, -1, -3, 0, -1, -4, 0, -1, 2, -4, -1, 0, -3, 1, -3, -2, -2,
     0, 0, -4, -3, 1, 1, 1, 0, 0, 0, 2, 1, 1, -3, -1, 0, 0, 0, 1, 3,
     1, 4, 4, -2, 0, 1, 6, 1, 0, 1, 0, 2, 2, 1, -2, 1, 5, -3, 0, 1] := by
  eta_coeff

end WeightTwoCusps
