module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 210

The eta expression is `η(z)^(-1) η(2z) η(3z) η(5z)^2 η(10z)^(-1) η(21z)^2 η(35z) η(42z)^(-1) η(105z)^(-1) η(210z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z) η(5z)^2 η(10z)^(-1) η(21z)^2 η(35z) η(42z)^(-1) η(105z)^(-1) η(210z)` at level 210. -/
abbrev cuspForm_210_eta_1m1_2p1_3p1_5p2_10m1_21p2_35p1_42m1_105m1_210p1 : gamma0CuspForms 210 :=
  etaQuotientCuspForm 210 sparse![210; 0 => -1, 1 => 1, 2 => 1, 4 => 2, 9 => -1, 20 => 2, 34 => 1, 41 => -1, 104 => -1, 209 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m1_2p1_3p1_5p2_10m1_21p2_35p1_42m1_105m1_210p1_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m1_2p1_3p1_5p2_10m1_21p2_35p1_42m1_105m1_210p1 =
    [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, -1, 0, 0, 0, -1, 1, -1, -1,
     0, -1, -1, -1, 0, -2, -1, -2, -1, -3, -2, -1, -2, 1, 0, -1, 1, 2, -3, 1,
     2, 0, 1, 1, 1, -1, 3, 4, 2, -1, 4, 0, -3, 5, 2, 0, 3, 1, 0, 4,
     3, 2, 1, 2, 4, 2, 1, 3, -2, -3, 1, -5, 0, 3, 0, 2, -1, -4, -7, -1,
     -5, -3, -4, -3, -2, -5, 3, 2, -1, -4, 0, -2, 3, 5, -1, -3, -5, 2, 1, 2] := by
  eta_coeff

end WeightTwoCusps
