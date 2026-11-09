module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 300

The eta expression is `η(z)^(-1) η(4z)^2 η(5z)^3 η(6z) η(10z)^(-1) η(12z)^(-1) η(15z)^(-1) η(25z) η(30z) η(50z)^(-1) η(100z)`; see
[the local level table](../../TABLE.md#level-300).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(4z)^2 η(5z)^3 η(6z) η(10z)^(-1) η(12z)^(-1) η(15z)^(-1) η(25z) η(30z) η(50z)^(-1) η(100z)` at level 300. -/
abbrev cuspForm_300_eta_1m1_4p2_5p3_6p1_10m1_12m1_15m1_25p1_30p1_50m1_100p1 : gamma0CuspForms 300 :=
  etaQuotientCuspForm 300 sparse![300; 0 => -1, 3 => 2, 4 => 3, 5 => 1, 9 => -1, 11 => -1, 14 => -1, 24 => 1, 29 => 1, 49 => -1, 99 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_300_eta_1m1_4p2_5p3_6p1_10m1_12m1_15m1_25p1_30p1_50m1_100p1_first_coeffs :
    first_coeffs 100 cuspForm_300_eta_1m1_4p2_5p3_6p1_10m1_12m1_15m1_25p1_30p1_50m1_100p1 =
    [0, 0, 0, 0, 1, 1, 2, 3, 3, 2, 3, 2, 0, 3, 1, 1, 1, 3, 0, 3,
     3, 2, 3, 0, 2, -1, 1, 0, 3, -2, 0, -1, -3, -3, 0, -1, -2, -3, -6, -3,
     -6, 0, -3, 0, -6, -2, -6, -6, 0, -3, 0, -5, 0, -3, -1, 0, -2, 0, -3, -4,
     -6, -3, 6, 3, 1, 2, -3, -6, -6, 3, -6, 2, 3, -6, -2, -1, 8, -6, 0, 0,
     -3, -5, -12, 0, -4, 0, 1, -3, -9, -2, 3, -1, 0, 6, -6, -4, -4, 0, 12, -1] := by
  eta_coeff

end WeightTwoCusps
