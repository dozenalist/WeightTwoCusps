module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 210

The eta expression is `η(z)^(-1) η(2z) η(3z) η(5z)^2 η(7z)^(-1) η(10z)^(-1) η(14z) η(15z)^(-1) η(21z)^2 η(30z) η(42z)^(-1) η(70z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z) η(5z)^2 η(7z)^(-1) η(10z)^(-1) η(14z) η(15z)^(-1) η(21z)^2 η(30z) η(42z)^(-1) η(70z)` at level 210. -/
abbrev cuspForm_210_eta_1m1_2p1_3p1_5p2_7m1_10m1_14p1_15m1_21p2_30p1_42m1_70p1 : gamma0CuspForms 210 :=
  etaQuotientCuspForm 210 sparse![210; 0 => -1, 1 => 1, 2 => 1, 4 => 2, 6 => -1, 9 => -1, 13 => 1, 14 => -1, 20 => 2, 29 => 1, 41 => -1, 69 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m1_2p1_3p1_5p2_7m1_10m1_14p1_15m1_21p2_30p1_42m1_70p1_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m1_2p1_3p1_5p2_7m1_10m1_14p1_15m1_21p2_30p1_42m1_70p1 =
    [0, 0, 0, 0, 1, 1, 1, 1, 1, 0, -1, 1, 1, 1, 0, 2, -1, -2, 1, 1,
     1, 0, 3, -2, -3, -1, 1, -1, -1, 2, -3, -4, -2, 0, 0, 0, 0, -2, -4, -1,
     0, 2, 0, 0, -2, -4, -1, -2, 3, -1, 1, -2, -2, 1, 0, 3, 1, 4, -3, -3,
     1, 1, 0, 1, 3, -4, -4, 2, -1, 0, 1, 2, -2, -2, 2, -2, -3, -1, 0, -2,
     0, 1, -3, 1, 2, -1, 3, 1, 3, -2, 3, 2, 0, 1, 0, 6, -1, 5, 3, 2] := by
  eta_coeff

end WeightTwoCusps
