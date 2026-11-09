module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 450

The eta expression is `η(5z)^(-1) η(9z)^2 η(10z) η(15z)^3 η(18z)^(-1) η(25z) η(30z)^(-1) η(75z)^(-1) η(150z)`; see
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

/-- The cuspidal eta quotient `η(5z)^(-1) η(9z)^2 η(10z) η(15z)^3 η(18z)^(-1) η(25z) η(30z)^(-1) η(75z)^(-1) η(150z)` at level 450. -/
abbrev cuspForm_450_eta_5m1_9p2_10p1_15p3_18m1_25p1_30m1_75m1_150p1 : gamma0CuspForms 450 :=
  etaQuotientCuspForm 450 sparse![450; 4 => -1, 8 => 2, 9 => 1, 14 => 3, 17 => -1, 24 => 1, 29 => -1, 74 => -1, 149 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_450_eta_5m1_9p2_10p1_15p3_18m1_25p1_30m1_75m1_150p1_first_coeffs :
    first_coeffs 100 cuspForm_450_eta_5m1_9p2_10p1_15p3_18m1_25p1_30m1_75m1_150p1 =
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, -2, 1, 0, 0, 0, -2,
     -1, 0, 0, 0, -2, -1, 0, 0, 0, 2, -1, 0, 0, 0, 2, -2, 0, 0, 0, 2,
     -1, 2, 0, 0, 4, -1, 2, 0, 0, 2, 1, 2, 0, 0, 2, -2, -2, 0, 0, -2,
     -1, -2, 0, 0, 4, 0, -2, 0, 0, 2, 2, -4, 0, 0, 0, 1, -2, 0, 0, -4,
     3, -2, 0, 0, -2, 4, 0, 0, 0, -6, 1, -6, 0, 0, -8, 0, -4, 0, 0, -2] := by
  eta_coeff

end WeightTwoCusps
