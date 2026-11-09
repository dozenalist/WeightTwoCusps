module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 210

The eta expression is `η(z)^(-1) η(2z) η(5z)^2 η(6z) η(7z) η(10z)^(-1) η(15z)^(-1) η(21z) η(30z) η(35z) η(42z)^(-1) η(70z)^(-1) η(105z)^(-1) η(210z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(5z)^2 η(6z) η(7z) η(10z)^(-1) η(15z)^(-1) η(21z) η(30z) η(35z) η(42z)^(-1) η(70z)^(-1) η(105z)^(-1) η(210z)^2` at level 210. -/
abbrev cuspForm_210_eta_1m1_2p1_5p2_6p1_7p1_10m1_15m1_21p1_30p1_35p1_42m1_70m1_105m1_210p2 : gamma0CuspForms 210 :=
  etaQuotientCuspForm 210 sparse![210; 0 => -1, 1 => 1, 4 => 2, 5 => 1, 6 => 1, 9 => -1, 14 => -1, 20 => 1, 29 => 1, 34 => 1, 41 => -1, 69 => -1, 104 => -1, 209 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m1_2p1_5p2_6p1_7p1_10m1_15m1_21p1_30p1_35p1_42m1_70m1_105m1_210p2_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m1_2p1_5p2_6p1_7p1_10m1_15m1_21p1_30p1_35p1_42m1_70m1_105m1_210p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 1, 1, 1,
     0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 2, -2, 1, -1, -3, -4, 0, -3,
     -3, 0, -2, -1, -4, -1, -3, 0, -4, -2, -3, -3, -4, -4, -1, -4, -2, 0, 1, -5,
     1, 3, -1, -1, 2, 2, -2, -1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 0, 5,
     3, 2, -6, 4, 2, -3, -1, 5, 0, -4, 6, 3, 5, -2, 7, 0, 2, -3, 3, 3] := by
  eta_coeff

end WeightTwoCusps
