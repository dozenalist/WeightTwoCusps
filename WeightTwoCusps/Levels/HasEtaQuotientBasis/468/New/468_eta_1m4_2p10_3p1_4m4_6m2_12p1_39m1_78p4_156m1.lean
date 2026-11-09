module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(6z)^(-2) η(12z) η(39z)^(-1) η(78z)^4 η(156z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(6z)^(-2) η(12z) η(39z)^(-1) η(78z)^4 η(156z)^(-1)` at level 468. -/
abbrev cuspForm_468_eta_1m4_2p10_3p1_4m4_6m2_12p1_39m1_78p4_156m1 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 5 => -2, 11 => 1, 38 => -1, 77 => 4, 155 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m4_2p10_3p1_4m4_6m2_12p1_39m1_78p4_156m1_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m4_2p10_3p1_4m4_6m2_12p1_39m1_78p4_156m1 =
    [0, 0, 0, 0, 0, 1, 4, 4, -1, 0, 4, 1, 0, 0, 2, 4, -4, -2, 0, -4,
     1, 0, 4, 0, -8, 0, -1, 0, 0, -2, 0, 0, 0, -4, -4, -2, 0, -4, 0, 0,
     -4, 3, 0, 0, -1, 4, 4, 1, 0, 0, 2, -8, 0, 2, 4, 0, -4, 0, -8, -1,
     4, 8, -2, -8, 0, -1, 0, 0, -2, 0, 4, 1, -4, -4, -2, 0, 0, 2, 0, -8,
     5, 0, -4, -3, -8, -4, 4, 8, -12, -3, -8, 0, 0, -8, 12, 2, 4, 4, -4, 4] := by
  eta_coeff

end WeightTwoCusps
