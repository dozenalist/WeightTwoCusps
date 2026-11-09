module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-2) η(2z)^5 η(3z) η(4z)^(-2) η(18z)^(-1) η(36z) η(39z)^(-2) η(78z)^4 η(117z) η(156z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(3z) η(4z)^(-2) η(18z)^(-1) η(36z) η(39z)^(-2) η(78z)^4 η(117z) η(156z)^(-1)` at level 468. -/
abbrev cuspForm_468_eta_1m2_2p5_3p1_4m2_18m1_36p1_39m2_78p4_117p1_156m1 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -2, 1 => 5, 2 => 1, 3 => -2, 17 => -1, 35 => 1, 38 => -2, 77 => 4, 116 => 1, 155 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m2_2p5_3p1_4m2_18m1_36p1_39m2_78p4_117p1_156m1_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m2_2p5_3p1_4m2_18m1_36p1_39m2_78p4_117p1_156m1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, -1, 0, 0, -1, -4, 0, 2, -2,
     0, -2, 0, 0, -1, 4, 0, 1, 2, 0, 0, 0, 0, 1, 0, 0, 2, -4, 0, 0,
     0, 0, -1, 4, 0, 2, 2, 0, 0, 4, 0, -3, 0, 0, -3, -12, 0, 4, -4, 0,
     -3, 0, 0, -1, 10, 0, 1, 4, 0, -2, -8, 0, 3, -2, 0, 3, -8, 0, 0, 4,
     0, -3, 10, 0, 6, 4, 0, -2, 2, 0, -2, 0, 0, -4, -12, 0, 2, 2, 0, 1] := by
  eta_coeff

end WeightTwoCusps
