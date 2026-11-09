module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 210

The eta expression is `η(z)^(-1) η(3z)^2 η(5z)^2 η(14z) η(15z)^(-1) η(21z) η(35z) η(42z)^(-1) η(70z)^(-1) η(210z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^2 η(5z)^2 η(14z) η(15z)^(-1) η(21z) η(35z) η(42z)^(-1) η(70z)^(-1) η(210z)` at level 210. -/
abbrev cuspForm_210_eta_1m1_3p2_5p2_14p1_15m1_21p1_35p1_42m1_70m1_210p1 : gamma0CuspForms 210 :=
  etaQuotientCuspForm 210 sparse![210; 0 => -1, 2 => 2, 4 => 2, 13 => 1, 14 => -1, 20 => 1, 34 => 1, 41 => -1, 69 => -1, 209 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m1_3p2_5p2_14p1_15m1_21p1_35p1_42m1_70m1_210p1_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m1_3p2_5p2_14p1_15m1_21p1_35p1_42m1_70m1_210p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 1, 3, 1, 2, 0, 4, 1, 2, 0, 3,
     0, -1, 0, 3, 1, -1, 1, 1, -1, -5, -1, 1, -2, -4, -1, -1, -6, -6, -3, 1,
     -6, -1, 0, -2, -8, -4, -3, -1, -4, 0, -1, -9, -7, -5, 0, -3, 3, 1, 2, -8,
     1, 0, -1, 1, 8, 2, -2, -4, 3, -3, -1, 8, 9, 1, -2, 5, 3, -1, -3, 11,
     9, -5, -3, 2, 0, -10, 8, 14, 12, -9, 7, 0, 3, -1, 12, 3, 2, -6, 0, 3] := by
  eta_coeff

end WeightTwoCusps
