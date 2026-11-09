module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-3) η(6z)^(-3) η(7z)^3 η(12z)^3 η(14z)^(-3) η(21z)^(-1) η(28z) η(42z)^3 η(84z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-3) η(6z)^(-3) η(7z)^3 η(12z)^3 η(14z)^(-3) η(21z)^(-1) η(28z) η(42z)^3 η(84z)^(-1)` at level 252. -/
abbrev cuspForm_252_eta_1m3_2p7_3p1_4m3_6m3_7p3_12p3_14m3_21m1_28p1_42p3_84m1 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -3, 1 => 7, 2 => 1, 3 => -3, 5 => -3, 6 => 3, 11 => 3, 13 => -3, 20 => -1, 27 => 1, 41 => 3, 83 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m3_2p7_3p1_4m3_6m3_7p3_12p3_14m3_21m1_28p1_42p3_84m1_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m3_2p7_3p1_4m3_6m3_7p3_12p3_14m3_21m1_28p1_42p3_84m1 =
    [0, 0, 1, 3, 2, 0, 2, 3, 4, 3, -4, 0, 6, 0, 0, -3, -5, 6, 1, -3,
     4, 0, 6, 6, -4, 3, 2, -3, 0, -6, -3, 3, -7, -6, 2, 0, 2, 6, -2, 3,
     8, -6, -1, -6, -13, 0, -7, -12, -4, -9, -3, 0, -4, 6, -4, -6, -3, -3, 2, -6,
     -13, -12, -2, 3, -1, -6, -4, 6, 14, 0, -5, 0, -5, 0, -6, -9, 4, 6, 5, -3,
     -6, 6, 14, 6, -7, 0, 2, 0, -9, -6, 2, 9, 5, 6, 12, 6, 18, 6, 1, 0] := by
  eta_coeff

end WeightTwoCusps
