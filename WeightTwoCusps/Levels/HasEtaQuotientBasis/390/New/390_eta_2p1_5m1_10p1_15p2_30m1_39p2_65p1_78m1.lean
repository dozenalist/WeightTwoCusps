module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 390

The eta expression is `η(2z) η(5z)^(-1) η(10z) η(15z)^2 η(30z)^(-1) η(39z)^2 η(65z) η(78z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(2z) η(5z)^(-1) η(10z) η(15z)^2 η(30z)^(-1) η(39z)^2 η(65z) η(78z)^(-1)` at level 390. -/
abbrev cuspForm_390_eta_2p1_5m1_10p1_15p2_30m1_39p2_65p1_78m1 : gamma0CuspForms 390 :=
  etaQuotientCuspForm 390 sparse![390; 1 => 1, 4 => -1, 9 => 1, 14 => 2, 29 => -1, 38 => 2, 64 => 1, 77 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_390_eta_2p1_5m1_10p1_15p2_30m1_39p2_65p1_78m1_first_coeffs :
    first_coeffs 100 cuspForm_390_eta_2p1_5m1_10p1_15p2_30m1_39p2_65p1_78m1 =
    [0, 0, 0, 1, 0, -1, 0, -1, 1, 0, -1, 0, -1, 2, 0, -1, 0, 0, 1, 0,
     0, 0, 1, 1, 0, 0, 0, 0, 1, 0, -1, 0, -2, -1, 0, 0, 0, -1, 1, 0,
     -1, 0, -2, -1, 2, 0, 2, -1, 1, 2, 0, 2, -3, 0, 2, 1, 0, -1, -1, 0,
     1, -2, -3, 1, 0, 0, 0, -3, -2, 2, 1, 4, 4, -1, 0, 1, 2, 0, -2, 2,
     1, 0, 2, -3, 0, 0, -2, -4, -1, 0, 1, -2, 1, -3, -2, 1, -2, 4, 0, -2] := by
  eta_coeff

end WeightTwoCusps
