module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-3) η(2z)^6 η(3z)^2 η(4z)^(-2) η(6z)^(-1) η(13z) η(26z)^(-1) η(156z) η(234z)^2 η(468z)^(-1)`; see
[the local level table](../../TABLE.md#level-468).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z)^2 η(4z)^(-2) η(6z)^(-1) η(13z) η(26z)^(-1) η(156z) η(234z)^2 η(468z)^(-1)` at level 468. -/
abbrev cuspForm_468_eta_1m3_2p6_3p2_4m2_6m1_13p1_26m1_156p1_234p2_468m1 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -3, 1 => 6, 2 => 2, 3 => -2, 5 => -1, 12 => 1, 25 => -1, 155 => 1, 233 => 2, 467 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m3_2p6_3p2_4m2_6m1_13p1_26m1_156p1_234p2_468m1_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m3_2p6_3p2_4m2_6m1_13p1_26m1_156p1_234p2_468m1 =
    [0, 0, 0, 0, 0, 0, 1, 3, 3, 2, 2, 3, 4, 1, 2, 4, 2, 4, 1, 1,
     -1, -2, 6, 0, -1, -2, -1, 2, -3, 2, -2, 1, 3, 2, 1, -8, 2, 2, 0, 0,
     -4, 2, 0, 2, 2, -4, -4, -1, 0, -4, -3, -6, -1, 0, -5, -2, -6, 4, -1, -2,
     0, -6, 2, -2, 6, 1, 0, 5, -4, 0, -6, -2, -1, -4, 4, -6, -5, 0, -1, 0,
     -8, -2, 0, -6, 0, 2, -2, -4, 4, 2, -2, 1, 2, 4, -2, 0, -5, -6, -5, 6] := by
  eta_coeff

end WeightTwoCusps
