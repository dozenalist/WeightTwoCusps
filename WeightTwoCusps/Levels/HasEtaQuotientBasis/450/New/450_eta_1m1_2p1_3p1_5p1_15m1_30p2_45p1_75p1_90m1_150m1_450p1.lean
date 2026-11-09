module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 450

The eta expression is `η(z)^(-1) η(2z) η(3z) η(5z) η(15z)^(-1) η(30z)^2 η(45z) η(75z) η(90z)^(-1) η(150z)^(-1) η(450z)`; see
[the local level table](../../TABLE.md#level-450).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z) η(5z) η(15z)^(-1) η(30z)^2 η(45z) η(75z) η(90z)^(-1) η(150z)^(-1) η(450z)` at level 450. -/
abbrev cuspForm_450_eta_1m1_2p1_3p1_5p1_15m1_30p2_45p1_75p1_90m1_150m1_450p1 : gamma0CuspForms 450 :=
  etaQuotientCuspForm 450 sparse![450; 0 => -1, 1 => 1, 2 => 1, 4 => 1, 14 => -1, 29 => 2, 44 => 1, 74 => 1, 89 => -1, 149 => -1, 449 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_450_eta_1m1_2p1_3p1_5p1_15m1_30p2_45p1_75p1_90m1_150m1_450p1_first_coeffs :
    first_coeffs 100 cuspForm_450_eta_1m1_2p1_3p1_5p1_15m1_30p2_45p1_75p1_90m1_150m1_450p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1,
     1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 2, 1, 2, 1, 0, 0, 2, 1,
     1, 0, 1, 0, 0, 1, 1, 0, -1, 1, -1, 0, 0, 1, -1, 0, 0, -1, 0, 0,
     0, 0, -1, -1, -2, -1, 1, 0, -1, -1, -2, 0, 0, 0, 0, -1, -2, -2, -2, -4,
     -2, -2, 0, -3, 0, -3, 0, -1, 0, 0, -2, -3, -5, -2, -3, -1, -2, 0, -4, -2] := by
  eta_coeff

end WeightTwoCusps
