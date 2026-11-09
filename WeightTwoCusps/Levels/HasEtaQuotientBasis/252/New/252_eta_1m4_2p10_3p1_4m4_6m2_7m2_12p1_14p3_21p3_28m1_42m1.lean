module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(6z)^(-2) η(7z)^(-2) η(12z) η(14z)^3 η(21z)^3 η(28z)^(-1) η(42z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^10 η(3z) η(4z)^(-4) η(6z)^(-2) η(7z)^(-2) η(12z) η(14z)^3 η(21z)^3 η(28z)^(-1) η(42z)^(-1)` at level 252. -/
abbrev cuspForm_252_eta_1m4_2p10_3p1_4m4_6m2_7m2_12p1_14p3_21p3_28m1_42m1 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -4, 1 => 10, 2 => 1, 3 => -4, 5 => -2, 6 => -2, 11 => 1, 13 => 3, 20 => 3, 27 => -1, 41 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m4_2p10_3p1_4m4_6m2_7m2_12p1_14p3_21p3_28m1_42m1_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m4_2p10_3p1_4m4_6m2_7m2_12p1_14p3_21p3_28m1_42m1 =
    [0, 1, 4, 4, -1, 0, 4, 1, 2, 8, 10, 2, -4, 6, 2, -2, 9, 12, 10, -8,
     -4, 2, -8, 6, 8, 13, -8, -16, 1, -14, -2, 0, 8, -8, -18, 0, -16, 4, 4, -2,
     -10, 0, 2, -14, 2, 0, 6, -28, 0, 1, -16, 8, -10, 14, -32, -20, 4, -2, 10, -12,
     2, -26, -12, 8, 1, -4, -8, 0, -24, -4, 8, -2, 14, 14, 0, -16, 8, 6, -2, 2,
     0, 18, -34, 0, -2, -16, 20, -4, 14, -16, 4, 8, 6, 4, 0, 4, -4, 30, 4, -4] := by
  eta_coeff

end WeightTwoCusps
