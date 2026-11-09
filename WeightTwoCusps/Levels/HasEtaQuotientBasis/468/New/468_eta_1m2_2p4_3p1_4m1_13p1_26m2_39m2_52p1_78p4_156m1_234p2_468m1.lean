module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-2) η(2z)^4 η(3z) η(4z)^(-1) η(13z) η(26z)^(-2) η(39z)^(-2) η(52z) η(78z)^4 η(156z)^(-1) η(234z)^2 η(468z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z) η(4z)^(-1) η(13z) η(26z)^(-2) η(39z)^(-2) η(52z) η(78z)^4 η(156z)^(-1) η(234z)^2 η(468z)^(-1)` at level 468. -/
abbrev cuspForm_468_eta_1m2_2p4_3p1_4m1_13p1_26m2_39m2_52p1_78p4_156m1_234p2_468m1 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -2, 1 => 4, 2 => 1, 3 => -1, 12 => 1, 25 => -2, 38 => -2, 51 => 1, 77 => 4, 155 => -1, 233 => 2, 467 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m2_2p4_3p1_4m1_13p1_26m2_39m2_52p1_78p4_156m1_234p2_468m1_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m2_2p4_3p1_4m1_13p1_26m2_39m2_52p1_78p4_156m1_234p2_468m1 =
    [0, 0, 0, 0, 1, 2, 1, 1, 1, 1, 1, -1, 1, 0, 0, 2, -2, -2, -3, 0,
     0, -3, -1, -2, 0, -2, 0, -1, -3, 2, 2, 2, -2, -1, 3, 2, 0, -1, 0, -1,
     3, 3, -3, -2, -1, 3, 0, -2, 0, 0, 1, -1, 1, -4, 1, 0, 0, 2, -4, 1,
     0, 2, -2, -2, 1, -1, 1, -2, 0, 0, -3, 0, -2, 0, 0, 1, 0, -6, 0, 0,
     2, 1, 1, 5, -1, 1, 3, 0, -1, 3, 6, 0, 2, 0, -3, -2, -3, 2, -1, -3] := by
  eta_coeff

end WeightTwoCusps
