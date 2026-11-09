module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 210

The eta expression is `η(z)^(-1) η(2z) η(5z)^3 η(7z) η(10z)^(-2) η(15z)^(-1) η(21z)^2 η(30z)^2 η(42z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(5z)^3 η(7z) η(10z)^(-2) η(15z)^(-1) η(21z)^2 η(30z)^2 η(42z)^(-1)` at level 210. -/
abbrev cuspForm_210_eta_1m1_2p1_5p3_7p1_10m2_15m1_21p2_30p2_42m1 : gamma0CuspForms 210 :=
  etaQuotientCuspForm 210 sparse![210; 0 => -1, 1 => 1, 4 => 3, 6 => 1, 9 => -2, 14 => -1, 20 => 2, 29 => 2, 41 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m1_2p1_5p3_7p1_10m2_15m1_21p2_30p2_42m1_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m1_2p1_5p3_7p1_10m2_15m1_21p2_30p2_42m1 =
    [0, 0, 1, 1, 1, 2, 2, 0, 1, 1, -1, 1, 1, 0, 2, 3, -1, 2, 1, -2,
     0, 2, 0, 0, 2, -2, -2, -3, 0, -3, -2, 0, -1, -2, -2, -2, -7, 0, -4, -3,
     1, 2, -4, -2, 0, -8, -2, -4, -1, -4, 3, 1, 0, -2, 2, 4, -6, 4, 0, 0,
     2, 6, -4, 0, 3, -11, 0, 2, 2, -4, 4, -2, -1, 4, -2, -3, -6, 4, -4, 3,
     0, 2, -4, 0, 1, -3, 8, 2, 2, 0, 9, 5, 0, 2, 6, 10, -4, 8, 5, 4] := by
  eta_coeff

end WeightTwoCusps
