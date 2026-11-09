module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 210

The eta expression is `η(z)^(-1) η(2z) η(3z) η(5z)^2 η(6z)^(-1) η(7z)^3 η(10z)^(-1) η(14z)^(-2) η(15z)^(-1) η(21z)^(-2) η(30z)^2 η(42z)^3`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z) η(5z)^2 η(6z)^(-1) η(7z)^3 η(10z)^(-1) η(14z)^(-2) η(15z)^(-1) η(21z)^(-2) η(30z)^2 η(42z)^3` at level 210. -/
abbrev cuspForm_210_eta_1m1_2p1_3p1_5p2_6m1_7p3_10m1_14m2_15m1_21m2_30p2_42p3 : gamma0CuspForms 210 :=
  etaQuotientCuspForm 210 sparse![210; 0 => -1, 1 => 1, 2 => 1, 4 => 2, 5 => -1, 6 => 3, 9 => -1, 13 => -2, 14 => -1, 20 => -2, 29 => 2, 41 => 3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m1_2p1_3p1_5p2_6m1_7p3_10m1_14m2_15m1_21m2_30p2_42p3_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m1_2p1_3p1_5p2_6m1_7p3_10m1_14m2_15m1_21m2_30p2_42p3 =
    [0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, -2, -2, -2, -3, -2, 0, 1, 1,
     1, 0, 3, 0, 1, -1, -1, -1, 1, -1, 2, 0, -2, 0, -1, 0, -1, -2, -5, 0,
     0, 3, 1, 2, 0, 4, 3, 3, 1, -2, -1, 1, -1, 1, 0, -2, 2, -2, 1, 2,
     -3, -1, 3, 1, 6, 1, -2, 2, 1, -1, -1, -4, 2, 4, 4, 1, -1, -2, -4, -3,
     0, -3, -5, -2, 0, 6, -1, 4, -5, -3, -3, -1, 0, -1, -7, -2, 5, -1, 5, -4] := by
  eta_coeff

end WeightTwoCusps
