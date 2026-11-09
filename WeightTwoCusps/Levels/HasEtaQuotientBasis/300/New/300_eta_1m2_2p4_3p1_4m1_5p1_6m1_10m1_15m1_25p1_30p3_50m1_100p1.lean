module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 300

The eta expression is `η(z)^(-2) η(2z)^4 η(3z) η(4z)^(-1) η(5z) η(6z)^(-1) η(10z)^(-1) η(15z)^(-1) η(25z) η(30z)^3 η(50z)^(-1) η(100z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z) η(4z)^(-1) η(5z) η(6z)^(-1) η(10z)^(-1) η(15z)^(-1) η(25z) η(30z)^3 η(50z)^(-1) η(100z)` at level 300. -/
abbrev cuspForm_300_eta_1m2_2p4_3p1_4m1_5p1_6m1_10m1_15m1_25p1_30p3_50m1_100p1 : gamma0CuspForms 300 :=
  etaQuotientCuspForm 300 sparse![300; 0 => -2, 1 => 4, 2 => 1, 3 => -1, 4 => 1, 5 => -1, 9 => -1, 14 => -1, 24 => 1, 29 => 3, 49 => -1, 99 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_300_eta_1m2_2p4_3p1_4m1_5p1_6m1_10m1_15m1_25p1_30p3_50m1_100p1_first_coeffs :
    first_coeffs 100 cuspForm_300_eta_1m2_2p4_3p1_4m1_5p1_6m1_10m1_15m1_25p1_30p3_50m1_100p1 =
    [0, 0, 0, 0, 0, 0, 1, 2, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0,
     1, 2, 0, 1, 1, 0, 0, 0, 2, 1, 1, -1, -2, -1, -1, 0, -1, -4, -2, -3,
     -1, 1, -1, 2, -2, 0, -2, -1, -1, -1, -1, -3, 2, -4, -1, 0, 1, 0, -2, -1,
     -3, 1, 5, 2, 2, 0, -2, 0, -3, 4, -4, -2, 1, -2, 0, 0, 3, -5, 2, 0,
     -3, -4, -4, 1, -3, 0, 0, -1, -4, -3, 1, 1, -1, 1, -2, 0, -1, 2, 5, -3] := by
  eta_coeff

end WeightTwoCusps
