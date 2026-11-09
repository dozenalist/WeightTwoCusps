module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 400

The eta expression is `η(z)^(-1) η(2z) η(4z)^3 η(8z)^(-2) η(20z)^(-1) η(25z) η(40z)^3 η(50z)^(-1) η(100z)^2 η(200z)^(-1)`; see
[the local level table](../../TABLE.md#level-400).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(4z)^3 η(8z)^(-2) η(20z)^(-1) η(25z) η(40z)^3 η(50z)^(-1) η(100z)^2 η(200z)^(-1)` at level 400. -/
abbrev cuspForm_400_eta_1m1_2p1_4p3_8m2_20m1_25p1_40p3_50m1_100p2_200m1 : gamma0CuspForms 400 :=
  etaQuotientCuspForm 400 sparse![400; 0 => -1, 1 => 1, 3 => 3, 7 => -2, 19 => -1, 24 => 1, 39 => 3, 49 => -1, 99 => 2, 199 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_400_eta_1m1_2p1_4p3_8m2_20m1_25p1_40p3_50m1_100p2_200m1_first_coeffs :
    first_coeffs 100 cuspForm_400_eta_1m1_2p1_4p3_8m2_20m1_25p1_40p3_50m1_100p2_200m1 =
    [0, 0, 0, 1, 1, 1, 2, -1, 0, 1, -1, 2, 1, 0, 1, 0, -1, -1, -1, 2,
     2, 1, 2, -2, 1, 1, 1, 1, -1, 1, 0, -2, 0, 0, -2, 4, 0, -1, 2, -2,
     0, 2, -1, 1, -1, -3, -1, -2, 0, -3, -1, 0, -1, 1, 1, -4, 2, 3, -1, 2,
     -4, -2, -2, -1, -1, -2, -3, 4, 3, -1, 4, -2, 0, 2, 3, 0, -1, 1, -2, -4,
     0, -5, -2, 2, -2, 2, -3, -1, 0, 3, 3, 0, -3, -3, -5, -4, 1, -3, 3, -2] := by
  eta_coeff

end WeightTwoCusps
