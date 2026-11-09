module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 210

The eta expression is `η(z)^(-1) η(3z) η(5z)^3 η(6z) η(7z) η(10z)^(-1) η(15z)^(-1) η(21z) η(35z) η(42z)^(-1) η(70z)^(-1) η(105z)^(-1) η(210z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z) η(5z)^3 η(6z) η(7z) η(10z)^(-1) η(15z)^(-1) η(21z) η(35z) η(42z)^(-1) η(70z)^(-1) η(105z)^(-1) η(210z)^2` at level 210. -/
abbrev cuspForm_210_eta_1m1_3p1_5p3_6p1_7p1_10m1_15m1_21p1_35p1_42m1_70m1_105m1_210p2 : gamma0CuspForms 210 :=
  etaQuotientCuspForm 210 sparse![210; 0 => -1, 2 => 1, 4 => 3, 5 => 1, 6 => 1, 9 => -1, 14 => -1, 20 => 1, 34 => 1, 41 => -1, 69 => -1, 104 => -1, 209 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m1_3p1_5p3_6p1_7p1_10m1_15m1_21p1_35p1_42m1_70m1_105m1_210p2_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m1_3p1_5p3_6p1_7p1_10m1_15m1_21p1_35p1_42m1_70m1_105m1_210p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 4, 2, 3, 1, 4,
     0, 2, 1, 4, 0, 1, 0, 2, 0, -2, 2, 2, 0, -4, -1, -2, -5, -8, -2, -1,
     -8, -3, -4, -3, -7, -2, -2, 1, -7, -3, -5, -8, -8, -6, -1, -3, -6, -2, 2, -10,
     -1, 2, 2, -2, 4, -2, -3, -7, 3, 0, 2, 7, 9, 2, 2, 3, 4, 5, 2, 12,
     10, -1, -7, 5, 3, -5, 3, 13, 5, -11, 7, 6, 8, -6, 13, 4, 8, -12, 5, 2] := by
  eta_coeff

end WeightTwoCusps
