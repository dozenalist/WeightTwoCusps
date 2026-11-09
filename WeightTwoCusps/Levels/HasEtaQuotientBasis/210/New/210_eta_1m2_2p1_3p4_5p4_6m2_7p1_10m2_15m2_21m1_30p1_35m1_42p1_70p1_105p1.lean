module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 210

The eta expression is `η(z)^(-2) η(2z) η(3z)^4 η(5z)^4 η(6z)^(-2) η(7z) η(10z)^(-2) η(15z)^(-2) η(21z)^(-1) η(30z) η(35z)^(-1) η(42z) η(70z) η(105z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^4 η(5z)^4 η(6z)^(-2) η(7z) η(10z)^(-2) η(15z)^(-2) η(21z)^(-1) η(30z) η(35z)^(-1) η(42z) η(70z) η(105z)` at level 210. -/
abbrev cuspForm_210_eta_1m2_2p1_3p4_5p4_6m2_7p1_10m2_15m2_21m1_30p1_35m1_42p1_70p1_105p1 : gamma0CuspForms 210 :=
  etaQuotientCuspForm 210 sparse![210; 0 => -2, 1 => 1, 2 => 4, 4 => 4, 5 => -2, 6 => 1, 9 => -2, 14 => -2, 20 => -1, 29 => 1, 34 => -1, 41 => 1, 69 => 1, 104 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m2_2p1_3p4_5p4_6m2_7p1_10m2_15m2_21m1_30p1_35m1_42p1_70p1_105p1_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m2_2p1_3p4_5p4_6m2_7p1_10m2_15m2_21m1_30p1_35m1_42p1_70p1_105p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 2, 4, 4, 6, 4, 4, -1, 2, -2, 0, -6, 0,
     -4, -1, -4, 4, 0, -2, -4, 0, 1, -4, 0, 0, 4, -4, 4, -1, 0, -16, -12, -8,
     -4, -4, 1, 6, 0, 4, 4, 12, -4, 0, -4, -4, -4, 2, 0, -4, 1, -2, 6, -12,
     0, -12, 0, -1, 8, 2, 8, -6, 0, 4, -1, 0, -4, 0, 0, 4, 8, 2, -6, 12,
     8, -4, 4, -4, -3, -10, 6, 16, 4, -4, 0, 2, 4, 6, -4, 6, -8, -8, 0, 2] := by
  eta_coeff

end WeightTwoCusps
