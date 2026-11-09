module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 468

The eta expression is `η(z)^(-3) η(2z)^6 η(3z)^2 η(4z)^(-2) η(6z)^(-1) η(13z) η(26z)^(-2) η(52z)^2 η(78z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z)^2 η(4z)^(-2) η(6z)^(-1) η(13z) η(26z)^(-2) η(52z)^2 η(78z)` at level 468. -/
abbrev cuspForm_468_eta_1m3_2p6_3p2_4m2_6m1_13p1_26m2_52p2_78p1 : gamma0CuspForms 468 :=
  etaQuotientCuspForm 468 sparse![468; 0 => -3, 1 => 6, 2 => 2, 3 => -2, 5 => -1, 12 => 1, 25 => -2, 51 => 2, 77 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_468_eta_1m3_2p6_3p2_4m2_6m1_13p1_26m2_52p2_78p1_first_coeffs :
    first_coeffs 100 cuspForm_468_eta_1m3_2p6_3p2_4m2_6m1_13p1_26m2_52p2_78p1 =
    [0, 0, 0, 0, 0, 0, 1, 3, 3, 2, 2, 3, 4, 1, 2, 4, 2, 4, 1, 1,
     -1, -2, 6, 0, -1, -2, -1, 2, -3, 2, -2, 1, 4, 5, 4, -6, 4, 5, 4, 1,
     -2, 6, 2, 6, 3, -3, -5, -3, 6, -4, -4, -8, -2, 2, -8, 0, -8, 5, 2, 0,
     1, -14, 4, 0, 6, 1, -4, 7, -4, 2, -4, -6, -5, -5, 4, -10, -8, -6, -2, 0,
     -13, -4, -6, -2, -1, 0, -2, -10, 6, 0, 4, 2, 2, 9, -6, 0, -11, -8, -6, 2] := by
  eta_coeff

end WeightTwoCusps
