module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 390

The eta expression is `η(5z)^(-1) η(6z) η(10z)^2 η(13z)^2 η(15z) η(26z)^(-1) η(30z)^(-1) η(39z)^(-1) η(78z) η(195z)`; see
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

/-- The cuspidal eta quotient `η(5z)^(-1) η(6z) η(10z)^2 η(13z)^2 η(15z) η(26z)^(-1) η(30z)^(-1) η(39z)^(-1) η(78z) η(195z)` at level 390. -/
abbrev cuspForm_390_eta_5m1_6p1_10p2_13p2_15p1_26m1_30m1_39m1_78p1_195p1 : gamma0CuspForms 390 :=
  etaQuotientCuspForm 390 sparse![390; 4 => -1, 5 => 1, 9 => 2, 12 => 2, 14 => 1, 25 => -1, 29 => -1, 38 => -1, 77 => 1, 194 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_390_eta_5m1_6p1_10p2_13p2_15p1_26m1_30m1_39m1_78p1_195p1_first_coeffs :
    first_coeffs 100 cuspForm_390_eta_5m1_6p1_10p2_13p2_15p1_26m1_30m1_39m1_78p1_195p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, -1, 0, 0, 0,
     0, -1, -1, -2, 0, 0, 0, -1, -2, 2, -1, 0, 0, 0, 2, 2, 1, 0, 0, 0,
     3, 0, 1, 2, 0, 1, 0, 0, 0, -1, 0, 0, 1, -2, 1, -5, 0, 1, -2, 0,
     -2, 1, 0, 0, 0, -2, -1, 2, 4, -1, -2, 0, -1, 2, -4, 1, 0, 0, 0, 1,
     -4, 1, -1, 0, 1, 0, 0, -1, 1, 0, -1, 1, 0, 1, -3, 2, 2, -2, 4, -2] := by
  eta_coeff

end WeightTwoCusps
