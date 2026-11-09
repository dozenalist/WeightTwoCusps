module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 210

The eta expression is `η(z)^(-1) η(3z)^3 η(5z) η(6z)^(-1) η(7z)^(-1) η(10z) η(14z)^2 η(15z)^(-1) η(21z) η(35z) η(42z)^(-1) η(70z)^(-1) η(105z)`; see
[the local level table](../../TABLE.md#level-210).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^3 η(5z) η(6z)^(-1) η(7z)^(-1) η(10z) η(14z)^2 η(15z)^(-1) η(21z) η(35z) η(42z)^(-1) η(70z)^(-1) η(105z)` at level 210. -/
abbrev cuspForm_210_eta_1m1_3p3_5p1_6m1_7m1_10p1_14p2_15m1_21p1_35p1_42m1_70m1_105p1 : gamma0CuspForms 210 :=
  etaQuotientCuspForm 210 sparse![210; 0 => -1, 2 => 3, 4 => 1, 5 => -1, 6 => -1, 9 => 1, 13 => 2, 14 => -1, 20 => 1, 34 => 1, 41 => -1, 69 => -1, 104 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m1_3p3_5p1_6m1_7m1_10p1_14p2_15m1_21p1_35p1_42m1_70m1_105p1_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m1_3p3_5p1_6m1_7m1_10p1_14p2_15m1_21p1_35p1_42m1_70m1_105p1 =
    [0, 0, 0, 1, 1, 2, 0, 2, 0, 2, 0, 4, 2, 1, -2, 1, 1, 0, 1, 4,
     1, -3, -3, 2, 0, -3, 2, 2, -1, -7, -2, 0, -4, -2, 1, 2, -8, -4, -4, -1,
     -4, 1, 4, -3, -5, -4, -6, -6, -2, 3, 3, -6, -2, -6, -3, -2, 10, 6, 2, -6,
     0, -4, -4, 2, 11, 1, -3, -1, 1, -4, -6, 11, 9, 0, -2, 2, 2, -8, 2, 9,
     9, -4, -1, 3, -2, -6, 9, 9, 13, -7, 5, -7, 0, 0, 11, 6, 0, -3, -5, 3] := by
  eta_coeff

end WeightTwoCusps
