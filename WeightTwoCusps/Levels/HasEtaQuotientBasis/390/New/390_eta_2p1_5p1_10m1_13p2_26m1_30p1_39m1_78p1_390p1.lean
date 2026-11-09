module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 390

The eta expression is `η(2z) η(5z) η(10z)^(-1) η(13z)^2 η(26z)^(-1) η(30z) η(39z)^(-1) η(78z) η(390z)`; see
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

/-- The cuspidal eta quotient `η(2z) η(5z) η(10z)^(-1) η(13z)^2 η(26z)^(-1) η(30z) η(39z)^(-1) η(78z) η(390z)` at level 390. -/
abbrev cuspForm_390_eta_2p1_5p1_10m1_13p2_26m1_30p1_39m1_78p1_390p1 : gamma0CuspForms 390 :=
  etaQuotientCuspForm 390 sparse![390; 1 => 1, 4 => 1, 9 => -1, 12 => 2, 25 => -1, 29 => 1, 38 => -1, 77 => 1, 389 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_390_eta_2p1_5p1_10m1_13p2_26m1_30p1_39m1_78p1_390p1_first_coeffs :
    first_coeffs 100 cuspForm_390_eta_2p1_5p1_10m1_13p2_26m1_30p1_39m1_78p1_390p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
     0, -1, 0, -1, -1, 0, 1, 0, 1, 1, 0, 0, -2, 1, 0, 0, 3, 2, 0, -1,
     0, -3, -2, -2, -2, 0, -1, 4, 1, -2, 0, 0, -2, 1, 2, 0, 4, 4, 1, 0,
     -1, -4, -1, -3, 0, 1, -1, 1, 2, 2, 0, 0, -3, -1, 3, 1, 4, 0, 0, 0,
     -1, -3, -6, -3, -2, 1, -2, 3, 0, -1, 0, 2, -3, -1, 2, 0, 2, 5, 3, 0] := by
  eta_coeff

end WeightTwoCusps
