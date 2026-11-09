module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 210

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^3 η(6z)^(-2) η(7z) η(14z)^(-1) η(21z)^(-1) η(35z)^(-1) η(42z) η(70z)^2 η(105z)^2 η(210z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^3 η(6z)^(-2) η(7z) η(14z)^(-1) η(21z)^(-1) η(35z)^(-1) η(42z) η(70z)^2 η(105z)^2 η(210z)^(-1)` at level 210. -/
abbrev cuspForm_210_eta_1m2_2p3_3p3_6m2_7p1_14m1_21m1_35m1_42p1_70p2_105p2_210m1 : gamma0CuspForms 210 :=
  etaQuotientCuspForm 210 sparse![210; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 6 => 1, 13 => -1, 20 => -1, 34 => -1, 41 => 1, 69 => 2, 104 => 2, 209 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m2_2p3_3p3_6m2_7p1_14m1_21m1_35m1_42p1_70p2_105p2_210m1_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m2_2p3_3p3_6m2_7p1_14m1_21m1_35m1_42p1_70p2_105p2_210m1 =
    [0, 0, 0, 0, 0, 1, 2, 2, 1, -1, 0, 0, 0, -1, -5, -3, -2, 1, 1, -3,
     0, 0, 1, 2, -2, -1, -1, 0, 3, -1, 2, 2, 2, 2, -1, 0, -1, 0, -1, -2,
     0, 3, 3, 4, -2, 2, 3, 0, -1, -6, -1, 1, -1, -1, -1, -3, 5, 0, 1, 0,
     -3, 1, 1, 4, 2, 1, -2, 2, 3, -1, -3, -4, -2, 2, -2, 1, 1, -5, 2, -1,
     -1, 1, -3, -2, 0, 4, 1, -2, -3, 3, -3, -1, 0, 3, 1, -2, 2, 0, 7, -2] := by
  eta_coeff

end WeightTwoCusps
