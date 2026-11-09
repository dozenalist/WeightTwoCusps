module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 400

The eta expression is `η(z)^(-1) η(2z)^2 η(20z)^(-1) η(25z)^(-1) η(40z)^5 η(50z)^3 η(80z)^(-2) η(100z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(20z)^(-1) η(25z)^(-1) η(40z)^5 η(50z)^3 η(80z)^(-2) η(100z)^(-1)` at level 400. -/
abbrev cuspForm_400_eta_1m1_2p2_20m1_25m1_40p5_50p3_80m2_100m1 : gamma0CuspForms 400 :=
  etaQuotientCuspForm 400 sparse![400; 0 => -1, 1 => 2, 19 => -1, 24 => -1, 39 => 5, 49 => 3, 79 => -2, 99 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_400_eta_1m1_2p2_20m1_25m1_40p5_50p3_80m2_100m1_first_coeffs :
    first_coeffs 100 cuspForm_400_eta_1m1_2p2_20m1_25m1_40p5_50p3_80m2_100m1 =
    [0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0,
     0, 0, 1, 2, 0, 1, 0, 1, 2, 0, 2, 0, 1, 1, 0, 0, 0, 2, 1, 0,
     0, 0, -2, -2, 0, -3, 0, 2, -1, 0, 2, 0, -4, 0, 0, 0, 0, -1, 0, 0,
     0, 0, -2, -4, 0, -2, 0, -3, -3, 0, -6, 0, -2, -5, 0, 0, 0, -4, -4, 0,
     0, 0, -1, 1, 0, 2, 0, -6, -3, 0, -4, 0, 6, 2, 0, 0, 0, -4, 1, 0] := by
  eta_coeff

end WeightTwoCusps
