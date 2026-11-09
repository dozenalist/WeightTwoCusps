module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 84

The eta expression is `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-2) η(6z)^(-2) η(12z) η(14z)^4 η(28z)^(-2) η(42z)^(-1) η(84z)`; see
[the local level table](../../TABLE.md#level-84).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-2) η(6z)^(-2) η(12z) η(14z)^4 η(28z)^(-2) η(42z)^(-1) η(84z)` at level 84. -/
abbrev cuspForm_84_eta_1m3_2p7_3p1_4m2_6m2_12p1_14p4_28m2_42m1_84p1 : gamma0CuspForms 84 :=
  etaQuotientCuspForm 84 sparse![84; 0 => -3, 1 => 7, 2 => 1, 3 => -2, 5 => -2, 11 => 1, 13 => 4, 27 => -2, 41 => -1, 83 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_84_eta_1m3_2p7_3p1_4m2_6m2_12p1_14p4_28m2_42m1_84p1_first_coeffs :
    first_coeffs 100 cuspForm_84_eta_1m3_2p7_3p1_4m2_6m2_12p1_14p4_28m2_42m1_84p1 =
    [0, 0, 1, 3, 2, 0, 1, 0, 1, 3, 0, 0, -1, 0, 1, -3, -4, -12, -8, 0,
     -6, 0, -6, -12, 1, 0, 2, -3, -4, 12, 3, 12, 7, -6, 12, 0, 11, 12, -4, 3,
     0, 12, 4, -12, 6, 0, 6, 24, -7, 0, -5, 0, 4, -12, 7, -12, 1, -3, -6, 12,
     -3, -24, -4, 3, 2, 12, 0, 12, -18, 0, 0, 0, -8, -24, -10, -9, 4, -12, -13, -24,
     6, 6, 0, -12, -4, 12, 8, 0, -6, 12, 0, 12, 6, 6, -12, -12, 7, 24, 1, 0] := by
  eta_coeff

end WeightTwoCusps
