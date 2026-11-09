module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 84

The eta expression is `η(z)^(-3) η(2z)^7 η(3z)^2 η(4z)^(-2) η(6z)^(-3) η(7z) η(12z) η(14z)^(-3) η(21z)^(-2) η(28z)^2 η(42z)^7 η(84z)^(-3)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z)^2 η(4z)^(-2) η(6z)^(-3) η(7z) η(12z) η(14z)^(-3) η(21z)^(-2) η(28z)^2 η(42z)^7 η(84z)^(-3)` at level 84. -/
abbrev cuspForm_84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3 : gamma0CuspForms 84 :=
  etaQuotientCuspForm 84 sparse![84; 0 => -3, 1 => 7, 2 => 2, 3 => -2, 5 => -3, 6 => 1, 11 => 1, 13 => -3, 20 => -2, 27 => 2, 41 => 7, 83 => -3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3_first_coeffs :
    first_coeffs 100 cuspForm_84_eta_1m3_2p7_3p2_4m2_6m3_7p1_12p1_14m3_21m2_28p2_42p7_84m3 =
    [0, 1, 3, 2, -1, -2, -2, 1, 1, -3, -4, -6, 0, 4, -1, 2, 3, 4, 3, -2,
     0, 2, 0, -2, -4, -9, 0, 4, -1, 2, 0, 4, 1, -2, 2, 2, -1, -2, 2, -8,
     0, 8, -2, 0, -8, -2, 8, 0, 4, 1, -7, 6, 12, 2, 4, 0, 1, 0, -10, 2,
     4, -4, -4, -3, -5, 4, 8, 8, 2, -6, 4, 2, 1, -2, -2, -6, -10, -2, 0, -4,
     -8, 5, 2, -10, 4, 4, 0, -4, -8, 4, -4, -4, 8, 0, -12, 8, -4, -14, 3, -6] := by
  eta_coeff

end WeightTwoCusps
