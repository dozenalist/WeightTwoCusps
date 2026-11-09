module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-3) η(2z)^6 η(3z)^3 η(4z)^(-2) η(6z)^(-3) η(7z)^(-1) η(9z)^(-1) η(12z) η(14z)^4 η(18z) η(21z)^(-1) η(28z)^(-2) η(42z) η(63z) η(84z) η(126z)^(-1)`; see
[the local level table](../../TABLE.md#level-252).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z)^3 η(4z)^(-2) η(6z)^(-3) η(7z)^(-1) η(9z)^(-1) η(12z) η(14z)^4 η(18z) η(21z)^(-1) η(28z)^(-2) η(42z) η(63z) η(84z) η(126z)^(-1)` at level 252. -/
abbrev cuspForm_252_eta_1m3_2p6_3p3_4m2_6m3_7m1_9m1_12p1_14p4_18p1_21m1_28m2_42p1_63p1_84p1_126m1 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -3, 1 => 6, 2 => 3, 3 => -2, 5 => -3, 6 => -1, 8 => -1, 11 => 1, 13 => 4, 17 => 1, 20 => -1, 27 => -2, 41 => 1, 62 => 1, 83 => 1, 125 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m3_2p6_3p3_4m2_6m3_7m1_9m1_12p1_14p4_18p1_21m1_28m2_42p1_63p1_84p1_126m1_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m3_2p6_3p3_4m2_6m3_7m1_9m1_12p1_14p4_18p1_21m1_28m2_42p1_63p1_84p1_126m1 =
    [0, 0, 1, 3, 3, 1, -1, 0, 3, 3, 5, 4, 1, 1, 0, 5, 0, -4, -2, -3,
     5, 0, -3, -4, -5, 2, -1, -3, -1, 0, 3, 6, -1, 2, -4, -1, 9, 2, 1, -13,
     -5, 4, 2, -6, -12, -8, -1, 2, -5, 0, -9, -8, -9, -2, 5, 0, -2, -3, 5, 1,
     -3, -9, -2, 3, -5, 4, 8, 4, 2, -8, 1, -2, -6, -8, -6, 7, 11, -4, -13, -4,
     -7, 6, -10, -3, -2, -2, 8, 0, 5, -2, -4, 5, 8, 6, 0, -10, 9, 2, 1, -8] := by
  eta_coeff

end WeightTwoCusps
