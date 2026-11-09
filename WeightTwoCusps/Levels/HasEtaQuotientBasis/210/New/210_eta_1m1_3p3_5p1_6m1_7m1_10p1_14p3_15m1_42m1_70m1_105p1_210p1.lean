module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 210

The eta expression is `η(z)^(-1) η(3z)^3 η(5z) η(6z)^(-1) η(7z)^(-1) η(10z) η(14z)^3 η(15z)^(-1) η(42z)^(-1) η(70z)^(-1) η(105z) η(210z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^3 η(5z) η(6z)^(-1) η(7z)^(-1) η(10z) η(14z)^3 η(15z)^(-1) η(42z)^(-1) η(70z)^(-1) η(105z) η(210z)` at level 210. -/
abbrev cuspForm_210_eta_1m1_3p3_5p1_6m1_7m1_10p1_14p3_15m1_42m1_70m1_105p1_210p1 : gamma0CuspForms 210 :=
  etaQuotientCuspForm 210 sparse![210; 0 => -1, 2 => 3, 4 => 1, 5 => -1, 6 => -1, 9 => 1, 13 => 3, 14 => -1, 41 => -1, 69 => -1, 104 => 1, 209 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m1_3p3_5p1_6m1_7m1_10p1_14p3_15m1_42m1_70m1_105p1_210p1_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m1_3p3_5p1_6m1_7m1_10p1_14p3_15m1_42m1_70m1_105p1_210p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 2, 0, 2, 0, 4, 2,
     1, -2, 1, 1, -1, 0, 2, 1, -5, -3, 0, 1, -6, 2, 1, 3, -8, -1, -1, -2,
     -6, 1, 1, -4, -7, -4, -1, -4, -1, 4, 0, -2, -2, -4, -2, -2, 7, 7, -2, 0,
     0, -3, -2, 1, 10, 3, -7, 2, 2, -2, -3, 5, 6, 1, -10, 0, -4, -7, 2, 1,
     8, 3, 1, 5, 2, -3, 12, -1, 13, -3, 5, -7, -1, 1, 14, 0, 0, -1, -7, 3] := by
  eta_coeff

end WeightTwoCusps
