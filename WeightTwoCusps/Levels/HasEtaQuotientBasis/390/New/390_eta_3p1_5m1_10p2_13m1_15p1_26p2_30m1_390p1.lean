module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 390

The eta expression is `η(3z) η(5z)^(-1) η(10z)^2 η(13z)^(-1) η(15z) η(26z)^2 η(30z)^(-1) η(390z)`; see
[the local level table](../../TABLE.md#level-390).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z) η(5z)^(-1) η(10z)^2 η(13z)^(-1) η(15z) η(26z)^2 η(30z)^(-1) η(390z)` at level 390. -/
abbrev cuspForm_390_eta_3p1_5m1_10p2_13m1_15p1_26p2_30m1_390p1 : gamma0CuspForms 390 :=
  etaQuotientCuspForm 390 sparse![390; 2 => 1, 4 => -1, 9 => 2, 12 => -1, 14 => 1, 25 => 2, 29 => -1, 389 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_390_eta_3p1_5m1_10p2_13m1_15p1_26p2_30m1_390p1_first_coeffs :
    first_coeffs 100 cuspForm_390_eta_3p1_5m1_10p2_13m1_15p1_26p2_30m1_390p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
     0, -1, 0, 1, -1, 0, -1, 0, 0, -1, 0, 1, 0, 1, -1, 0, 1, -1, 0, 0,
     0, 1, -1, 0, 2, 0, 1, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 3, 0, -2,
     -1, 0, 1, -4, 0, -1, 1, -1, -2, 2, 0, 0, -1, 0, 1, 0, -3, 0, -1, 2,
     1, -1, 2, 3, -1, 0, 0, 1, 0, 1, 0, -2, -1, -1, 0, 0, 3, -1, -3, 1] := by
  eta_coeff

end WeightTwoCusps
