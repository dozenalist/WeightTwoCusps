module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 180

The eta expression is `η(z)^(-2) η(2z) η(3z)^5 η(5z)^2 η(6z)^(-1) η(9z)^(-1) η(10z)^(-1) η(15z)^(-2) η(30z)^2 η(90z)`; see
[the local level table](../../TABLE.md#level-180).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^5 η(5z)^2 η(6z)^(-1) η(9z)^(-1) η(10z)^(-1) η(15z)^(-2) η(30z)^2 η(90z)` at level 180. -/
abbrev cuspForm_180_eta_1m2_2p1_3p5_5p2_6m1_9m1_10m1_15m2_30p2_90p1 : gamma0CuspForms 180 :=
  etaQuotientCuspForm 180 sparse![180; 0 => -2, 1 => 1, 2 => 5, 4 => 2, 5 => -1, 8 => -1, 9 => -1, 14 => -2, 29 => 2, 89 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_180_eta_1m2_2p1_3p5_5p2_6m1_9m1_10m1_15m2_30p2_90p1_first_coeffs :
    first_coeffs 100 cuspForm_180_eta_1m2_2p1_3p5_5p2_6m1_9m1_10m1_15m2_30p2_90p1 =
    [0, 0, 0, 0, 0, 1, 2, 4, 3, 4, 2, 2, -2, -2, 0, 0, 0, -3, 2, -4,
     -2, -4, 6, 2, 2, 2, 0, -4, -6, 2, -2, -4, -6, 0, -12, -7, -2, 6, -3, 0,
     2, -2, -8, -2, 6, -4, 0, -5, -2, -8, 0, 8, 6, 1, 2, 2, 0, 0, 0, 6,
     2, 0, 0, 4, 0, 3, 0, 6, -3, -4, -2, -2, 2, 0, 6, 0, 0, 1, 4, 0,
     1, 0, 6, -1, 8, 2, 0, -8, 6, 2, -2, 4, 0, 8, 0, 13, 2, -4, 3, 0] := by
  eta_coeff

end WeightTwoCusps
