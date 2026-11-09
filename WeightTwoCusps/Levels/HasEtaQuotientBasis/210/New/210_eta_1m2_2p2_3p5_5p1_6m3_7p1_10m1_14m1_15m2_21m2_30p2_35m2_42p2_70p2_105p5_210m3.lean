module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 210

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^5 η(5z) η(6z)^(-3) η(7z) η(10z)^(-1) η(14z)^(-1) η(15z)^(-2) η(21z)^(-2) η(30z)^2 η(35z)^(-2) η(42z)^2 η(70z)^2 η(105z)^5 η(210z)^(-3)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^5 η(5z) η(6z)^(-3) η(7z) η(10z)^(-1) η(14z)^(-1) η(15z)^(-2) η(21z)^(-2) η(30z)^2 η(35z)^(-2) η(42z)^2 η(70z)^2 η(105z)^5 η(210z)^(-3)` at level 210. -/
abbrev cuspForm_210_eta_1m2_2p2_3p5_5p1_6m3_7p1_10m1_14m1_15m2_21m2_30p2_35m2_42p2_70p2_105p5_210m3 : gamma0CuspForms 210 :=
  etaQuotientCuspForm 210 sparse![210; 0 => -2, 1 => 2, 2 => 5, 4 => 1, 5 => -3, 6 => 1, 9 => -1, 13 => -1, 14 => -2, 20 => -2, 29 => 2, 34 => -2, 41 => 2, 69 => 2, 104 => 5, 209 => -3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m2_2p2_3p5_5p1_6m3_7p1_10m1_14m1_15m2_21m2_30p2_35m2_42p2_70p2_105p5_210m3_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m2_2p2_3p5_5p1_6m3_7p1_10m1_14m1_15m2_21m2_30p2_35m2_42p2_70p2_105p5_210m3 =
    [0, 1, 2, 3, 1, -1, -2, -2, -1, -3, -3, -5, -4, 0, 4, 5, 4, 2, 4, 1,
     1, 0, -4, -3, -3, 2, -1, 0, -2, 1, -5, 1, 0, 0, -1, 0, 7, 8, 9, 5,
     2, -7, -2, -10, 0, -9, -3, -5, 3, 5, 5, 3, -3, -1, -4, 5, -5, 1, -4, 8,
     6, 12, 3, -2, -11, -6, 0, -4, -3, -11, 3, 2, 9, 5, 4, -2, 1, 3, 1, 1,
     -8, 0, -5, 4, 1, -2, -8, -6, -4, 1, 7, 0, 5, -7, 6, 1, 12, 0, -4, -7] := by
  eta_coeff

end WeightTwoCusps
