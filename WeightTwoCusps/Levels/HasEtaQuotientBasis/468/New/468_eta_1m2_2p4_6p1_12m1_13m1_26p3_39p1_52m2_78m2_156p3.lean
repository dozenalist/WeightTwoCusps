module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-2) η(2z)^4 η(6z) η(12z)^(-1) η(13z)^(-1) η(26z)^3 η(39z) η(52z)^(-2) η(78z)^(-2) η(156z)^3`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(6z) η(12z)^(-1) η(13z)^(-1) η(26z)^3 η(39z) η(52z)^(-2) η(78z)^(-2) η(156z)^3` at level 468. -/
abbrev cuspForm_468_eta_1m2_2p4_6p1_12m1_13m1_26p3_39p1_52m2_78m2_156p3 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -2, 1 => 4, 5 => 1, 11 => -1, 12 => -1, 25 => 3, 38 => 1, 51 => -2, 77 => -2, 155 => 3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m2_2p4_6p1_12m1_13m1_26p3_39p1_52m2_78m2_156p3_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m2_2p4_6p1_12m1_13m1_26p3_39p1_52m2_78m2_156p3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 2, 2, 0, 2,
     0, -1, 0, 0, 2, -2, 1, 2, 1, 4, 0, 0, -2, 0, -1, -4, 0, 0, 0, -1,
     -4, -1, 0, -4, 0, -7, -4, -3, -4, 0, -4, 6, -1, -4, -3, -4, -4, -2, 1, -4,
     -3, 2, 2, 1, 6, 0, 2, -4, -2, -2, -6, 5, 6, 4, 2, 2, 3, 2, 1, 8,
     -3, 0, 6, -2, 3, 6, 7, 2, 0, 5, -6, 0, 4, 0, 4, -2, 8, -4, -2, 6] := by
  eta_coeff

end WeightTwoCusps
