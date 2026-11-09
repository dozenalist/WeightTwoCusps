module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 210

The eta expression is `η(z)^(-1) η(3z) η(5z)^3 η(6z) η(7z) η(10z)^(-1) η(14z) η(15z)^(-1) η(42z)^(-1) η(70z)^(-1) η(105z)^(-1) η(210z)^3`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z) η(5z)^3 η(6z) η(7z) η(10z)^(-1) η(14z) η(15z)^(-1) η(42z)^(-1) η(70z)^(-1) η(105z)^(-1) η(210z)^3` at level 210. -/
abbrev cuspForm_210_eta_1m1_3p1_5p3_6p1_7p1_10m1_14p1_15m1_42m1_70m1_105m1_210p3 : gamma0CuspForms 210 :=
  etaQuotientCuspForm 210 sparse![210; 0 => -1, 2 => 1, 4 => 3, 5 => 1, 6 => 1, 9 => -1, 13 => 1, 14 => -1, 41 => -1, 69 => -1, 104 => -1, 209 => 3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m1_3p1_5p3_6p1_7p1_10m1_14p1_15m1_42m1_70m1_105m1_210p3_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m1_3p1_5p3_6p1_7p1_10m1_14p1_15m1_42m1_70m1_105m1_210p3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1,
     2, 2, 4, 2, 3, 1, 4, 0, 2, 1, 4, 0, 0, -1, 0, -2, -6, 0, -1, 0,
     -7, 1, -2, -2, -10, 1, -2, -5, -7, -4, -4, -7, -7, -2, 1, -4, -3, -3, -2, -4,
     -4, 5, 1, 0, 6, 3, -6, 0, 3, 3, -1, 5, 11, -1, -3, 4, 1, 3, -3, 0,
     7, -2, -11, 4, 2, 2, 4, 9, 10, -7, 4, 5, 2, -2, 16, -4, 8, -4, 7, 2] := by
  eta_coeff

end WeightTwoCusps
