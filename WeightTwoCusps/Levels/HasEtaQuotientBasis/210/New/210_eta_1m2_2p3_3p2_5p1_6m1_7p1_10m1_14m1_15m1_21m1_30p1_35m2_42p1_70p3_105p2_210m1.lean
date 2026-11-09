module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 210

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^2 η(5z) η(6z)^(-1) η(7z) η(10z)^(-1) η(14z)^(-1) η(15z)^(-1) η(21z)^(-1) η(30z) η(35z)^(-2) η(42z) η(70z)^3 η(105z)^2 η(210z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^2 η(5z) η(6z)^(-1) η(7z) η(10z)^(-1) η(14z)^(-1) η(15z)^(-1) η(21z)^(-1) η(30z) η(35z)^(-2) η(42z) η(70z)^3 η(105z)^2 η(210z)^(-1)` at level 210. -/
abbrev cuspForm_210_eta_1m2_2p3_3p2_5p1_6m1_7p1_10m1_14m1_15m1_21m1_30p1_35m2_42p1_70p3_105p2_210m1 : gamma0CuspForms 210 :=
  etaQuotientCuspForm 210 sparse![210; 0 => -2, 1 => 3, 2 => 2, 4 => 1, 5 => -1, 6 => 1, 9 => -1, 13 => -1, 14 => -1, 20 => -1, 29 => 1, 34 => -2, 41 => 1, 69 => 3, 104 => 2, 209 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m2_2p3_3p2_5p1_6m1_7p1_10m1_14m1_15m1_21m1_30p1_35m2_42p1_70p3_105p2_210m1_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m2_2p3_3p2_5p1_6m1_7p1_10m1_14m1_15m1_21m1_30p1_35m2_42p1_70p3_105p2_210m1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 2, 1, 1, 0, -1, -1, -3, -2, -1, -1,
     -1, 0, 1, 1, 0, 0, 0, -2, 0, 0, 0, 0, 0, -2, -1, -1, -1, -1, -2, 0,
     0, 3, 1, 3, 1, 3, 0, 0, 1, -2, -2, 0, 2, -2, 2, -3, 1, -3, -2, -3,
     -1, -1, 0, 1, 0, 4, -1, 3, -3, 2, -1, 0, -6, -1, 2, 1, 3, -1, 1, -2,
     2, -2, 3, 0, 0, 0, 6, 4, 1, 1, -3, 1, -5, -1, -5, -2, 1, 5, 2, 1] := by
  eta_coeff

end WeightTwoCusps
