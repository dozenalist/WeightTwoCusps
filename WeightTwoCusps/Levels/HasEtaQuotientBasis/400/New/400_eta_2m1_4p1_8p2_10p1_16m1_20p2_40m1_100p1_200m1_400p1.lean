module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 400

The eta expression is `η(2z)^(-1) η(4z) η(8z)^2 η(10z) η(16z)^(-1) η(20z)^2 η(40z)^(-1) η(100z) η(200z)^(-1) η(400z)`; see
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

/-- The cuspidal eta quotient `η(2z)^(-1) η(4z) η(8z)^2 η(10z) η(16z)^(-1) η(20z)^2 η(40z)^(-1) η(100z) η(200z)^(-1) η(400z)` at level 400. -/
abbrev cuspForm_400_eta_2m1_4p1_8p2_10p1_16m1_20p2_40m1_100p1_200m1_400p1 : gamma0CuspForms 400 :=
  etaQuotientCuspForm 400 sparse![400; 1 => -1, 3 => 1, 7 => 2, 9 => 1, 15 => -1, 19 => 2, 39 => -1, 99 => 1, 199 => -1, 399 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_400_eta_2m1_4p1_8p2_10p1_16m1_20p2_40m1_100p1_200m1_400p1_first_coeffs :
    first_coeffs 100 cuspForm_400_eta_2m1_4p1_8p2_10p1_16m1_20p2_40m1_100p1_200m1_400p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 2,
     0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, -2, 0, -3, 0, -1, 0, -6,
     0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, -4, 0, -1, 0, 2, 0, -4, 0, 4,
     0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, -2, 0, 3, 0, -1, 0, 2, 0, 0,
     0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 2, 0, -2, 0, 4, 0, 7, 0, 2] := by
  eta_coeff

end WeightTwoCusps
