module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 210

The eta expression is `η(z)^(-1) η(2z) η(3z) η(5z) η(15z)^(-1) η(21z)^2 η(30z) η(35z)^2 η(42z)^(-1) η(70z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z) η(5z) η(15z)^(-1) η(21z)^2 η(30z) η(35z)^2 η(42z)^(-1) η(70z)^(-1)` at level 210. -/
abbrev cuspForm_210_eta_1m1_2p1_3p1_5p1_15m1_21p2_30p1_35p2_42m1_70m1 : gamma0CuspForms 210 :=
  etaQuotientCuspForm 210 sparse![210; 0 => -1, 1 => 1, 2 => 1, 4 => 1, 14 => -1, 20 => 2, 29 => 1, 34 => 2, 41 => -1, 69 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m1_2p1_3p1_5p1_15m1_21p2_30p1_35p2_42m1_70m1_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m1_2p1_3p1_5p1_15m1_21p2_30p1_35p2_42m1_70m1 =
    [0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 2, 1, 2,
     1, 0, -2, 0, -1, -1, -2, -1, 0, -2, -1, 0, 1, -2, 2, 0, -3, -4, -4, -4,
     -5, -4, 0, -2, -6, -3, 0, 0, -1, 1, -1, -2, -8, -2, -3, -6, 0, 4, 0, -2,
     3, 4, 4, 0, 5, 2, -2, -6, 2, -4, -2, 0, 1, 4, 0, 5, 6, 0, -4, 10,
     3, -1, -8, 0, -2, 0, 2, 10, 2, -4, 7, 0, 4, 2, 12, 0, 1, -8, 1, 0] := by
  eta_coeff

end WeightTwoCusps
