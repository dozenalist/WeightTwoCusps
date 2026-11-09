module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 180

The eta expression is `η(z)^(-2) η(2z) η(3z)^5 η(5z)^2 η(6z)^(-2) η(10z)^(-1) η(15z)^(-1) η(30z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^5 η(5z)^2 η(6z)^(-2) η(10z)^(-1) η(15z)^(-1) η(30z)^2` at level 180. -/
abbrev cuspForm_180_eta_1m2_2p1_3p5_5p2_6m2_10m1_15m1_30p2 : gamma0CuspForms 180 :=
  etaQuotientCuspForm 180 sparse![180; 0 => -2, 1 => 1, 2 => 5, 4 => 2, 5 => -2, 9 => -1, 14 => -1, 29 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_180_eta_1m2_2p1_3p5_5p2_6m2_10m1_15m1_30p2_first_coeffs :
    first_coeffs 100 cuspForm_180_eta_1m2_2p1_3p5_5p2_6m2_10m1_15m1_30p2 =
    [0, 0, 1, 2, 4, 3, 4, 2, 3, 0, 2, 2, 2, -2, -2, 0, 0, 0, 2, 4,
     -1, -4, -2, 0, -4, 0, 0, 2, -6, -2, -2, -4, -3, -4, -8, -12, -8, -6, -6, 0,
     -2, -4, -12, 4, 2, -2, 0, -2, -6, -8, 1, 8, -2, 0, 4, -2, -2, 0, 8, 2,
     8, 4, 4, -4, -4, 6, -4, 8, -4, 0, -6, 0, 10, 4, 8, 2, 4, 2, 4, -4,
     1, 0, 14, 2, 12, 4, 0, -8, 14, 8, -4, 4, 0, 8, 4, 26, 20, 0, 7, 4] := by
  eta_coeff

end WeightTwoCusps
