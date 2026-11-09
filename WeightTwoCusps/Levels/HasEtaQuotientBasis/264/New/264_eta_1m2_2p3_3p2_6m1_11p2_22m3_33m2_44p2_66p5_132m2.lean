module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 264

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^2 η(6z)^(-1) η(11z)^2 η(22z)^(-3) η(33z)^(-2) η(44z)^2 η(66z)^5 η(132z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^2 η(6z)^(-1) η(11z)^2 η(22z)^(-3) η(33z)^(-2) η(44z)^2 η(66z)^5 η(132z)^(-2)` at level 264. -/
abbrev cuspForm_264_eta_1m2_2p3_3p2_6m1_11p2_22m3_33m2_44p2_66p5_132m2 : gamma0CuspForms 264 :=
  etaQuotientCuspForm 264 sparse![264; 0 => -2, 1 => 3, 2 => 2, 5 => -1, 10 => 2, 21 => -3, 32 => -2, 43 => 2, 65 => 5, 131 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_264_eta_1m2_2p3_3p2_6m1_11p2_22m3_33m2_44p2_66p5_132m2_first_coeffs :
    first_coeffs 100 cuspForm_264_eta_1m2_2p3_3p2_6m1_11p2_22m3_33m2_44p2_66p5_132m2 =
    [0, 0, 1, 2, 2, 2, 1, 2, 2, 2, 3, 0, 2, 0, -2, -2, -4, 2, -2, -2,
     -2, -6, 1, -2, 2, 2, 0, 6, -4, 2, 3, 2, 8, -2, 2, -4, -4, 2, -4, 4,
     -2, -6, -2, -6, 2, 0, 1, 4, -4, 0, -6, -2, 8, 0, 1, -2, -4, -2, -8, 2,
     -2, 0, 1, -14, -4, -4, 1, -2, -4, 6, -6, -2, -4, -4, 9, 0, 0, -2, 0, -2,
     -8, 4, 0, 0, -4, -12, -6, -2, 2, -6, 0, 4, -6, -6, 0, 8, 8, 6, -3, -2] := by
  eta_coeff

end WeightTwoCusps
