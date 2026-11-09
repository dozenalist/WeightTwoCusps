module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 390

The eta expression is `η(3z) η(5z)^2 η(10z)^(-1) η(13z)^(-1) η(15z)^(-1) η(26z)^2 η(30z) η(39z) η(78z)^(-1) η(390z)`; see
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

/-- The cuspidal eta quotient `η(3z) η(5z)^2 η(10z)^(-1) η(13z)^(-1) η(15z)^(-1) η(26z)^2 η(30z) η(39z) η(78z)^(-1) η(390z)` at level 390. -/
abbrev cuspForm_390_eta_3p1_5p2_10m1_13m1_15m1_26p2_30p1_39p1_78m1_390p1 : gamma0CuspForms 390 :=
  etaQuotientCuspForm 390 sparse![390; 2 => 1, 4 => 2, 9 => -1, 12 => -1, 14 => -1, 25 => 2, 29 => 1, 38 => 1, 77 => -1, 389 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_390_eta_3p1_5p2_10m1_13m1_15m1_26p2_30p1_39p1_78m1_390p1_first_coeffs :
    first_coeffs 100 cuspForm_390_eta_3p1_5p2_10m1_13m1_15m1_26p2_30p1_39p1_78m1_390p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
     -1, 0, -2, -1, 0, 2, 0, 0, 2, 0, 1, 0, 2, -1, 0, -3, -1, -2, 2, 0,
     0, 2, 0, -2, 0, 2, 0, 2, -1, 0, -3, 0, 0, -1, 0, 0, -2, 0, 2, 0,
     2, 0, 0, -1, 0, 0, -1, 0, 0, -1, 2, 2, 1, 2, 2, 1, 0, -3, 0, 0,
     -2, 0, -2, 2, -2, 0, 2, 1, -4, 2, -1, 0, 0, 0, 0, 0, 0, 0, 0, -2] := by
  eta_coeff

end WeightTwoCusps
