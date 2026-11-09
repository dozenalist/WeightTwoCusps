module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 210

The eta expression is `η(z)^(-1) η(2z) η(3z) η(5z)^2 η(6z)^(-1) η(7z)^2 η(10z)^(-1) η(14z)^(-1) η(15z)^(-2) η(21z)^(-2) η(30z)^3 η(35z)^(-1) η(42z)^3 η(70z) η(105z) η(210z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z) η(5z)^2 η(6z)^(-1) η(7z)^2 η(10z)^(-1) η(14z)^(-1) η(15z)^(-2) η(21z)^(-2) η(30z)^3 η(35z)^(-1) η(42z)^3 η(70z) η(105z) η(210z)^(-1)` at level 210. -/
abbrev cuspForm_210_eta_1m1_2p1_3p1_5p2_6m1_7p2_10m1_14m1_15m2_21m2_30p3_35m1_42p3_70p1_105p1_210m1 : gamma0CuspForms 210 :=
  etaQuotientCuspForm 210 sparse![210; 0 => -1, 1 => 1, 2 => 1, 4 => 2, 5 => -1, 6 => 2, 9 => -1, 13 => -1, 14 => -2, 20 => -2, 29 => 3, 34 => -1, 41 => 3, 69 => 1, 104 => 1, 209 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m1_2p1_3p1_5p2_6m1_7p2_10m1_14m1_15m2_21m2_30p3_35m1_42p3_70p1_105p1_210m1_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m1_2p1_3p1_5p2_6m1_7p2_10m1_14m1_15m2_21m2_30p3_35m1_42p3_70p1_105p1_210m1 =
    [0, 0, 0, 1, 1, 1, 1, 1, 0, 0, -1, -1, -1, -2, -1, 0, 1, 0, 1, 0,
     2, 0, 2, 0, 0, -1, 0, 0, 0, 0, -2, -1, -3, 0, -3, 0, -4, 1, 1, 3,
     1, 4, 0, 1, 1, -2, -1, -5, -2, -2, 1, -1, 3, -1, 2, -2, 1, -2, -3, -1,
     1, 3, 1, 1, -1, 1, -1, 3, -2, -1, 0, -2, 2, 2, 2, 1, -2, -2, 4, -2,
     -2, -2, 0, 2, 1, 5, 2, 0, -3, 0, 0, 0, -2, -2, 0, -1, 6, 3, 2, -3] := by
  eta_coeff

end WeightTwoCusps
