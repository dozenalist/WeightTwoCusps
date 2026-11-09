module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 210

The eta expression is `η(z)^(-2) η(2z)^4 η(3z) η(5z) η(6z)^(-2) η(7z) η(10z)^(-2) η(14z)^(-1) η(15z)^(-2) η(30z)^4 η(42z) η(70z) η(105z) η(210z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z) η(5z) η(6z)^(-2) η(7z) η(10z)^(-2) η(14z)^(-1) η(15z)^(-2) η(30z)^4 η(42z) η(70z) η(105z) η(210z)^(-1)` at level 210. -/
abbrev cuspForm_210_eta_1m2_2p4_3p1_5p1_6m2_7p1_10m2_14m1_15m2_30p4_42p1_70p1_105p1_210m1 : gamma0CuspForms 210 :=
  etaQuotientCuspForm 210 sparse![210; 0 => -2, 1 => 4, 2 => 1, 4 => 1, 5 => -2, 6 => 1, 9 => -2, 13 => -1, 14 => -2, 29 => 4, 41 => 1, 69 => 1, 104 => 1, 209 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m2_2p4_3p1_5p1_6m2_7p1_10m2_14m1_15m2_30p4_42p1_70p1_105p1_210m1_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m2_2p4_3p1_5p1_6m2_7p1_10m2_14m1_15m2_30p4_42p1_70p1_105p1_210m1 =
    [0, 0, 0, 1, 2, 1, 1, 0, -2, 0, 0, -2, -2, -1, 0, 2, 4, 1, 0, 1,
     -1, 0, 0, -2, 0, -2, -1, 1, 0, 2, -2, -3, -2, 2, 2, 0, 0, -4, -2, 2,
     1, -2, 0, 0, 2, -1, 2, 0, -5, 0, 0, -2, 0, 4, -1, 3, 0, 0, -2, -1,
     0, -2, 3, 0, 2, 0, 0, -2, -4, 0, 0, -6, 6, 4, 0, 2, -1, 0, -2, 2,
     0, -2, -2, 4, 0, -4, -2, 1, -6, 2, 3, 0, 4, 4, 3, 4, 7, -7, 0, -6] := by
  eta_coeff

end WeightTwoCusps
