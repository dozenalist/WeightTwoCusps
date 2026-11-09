module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 180

The eta expression is `η(z)^(-3) η(2z)^5 η(3z) η(5z)^3 η(6z)^(-1) η(10z)^(-1) η(15z)^(-1) η(30z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^5 η(3z) η(5z)^3 η(6z)^(-1) η(10z)^(-1) η(15z)^(-1) η(30z)` at level 180. -/
abbrev cuspForm_180_eta_1m3_2p5_3p1_5p3_6m1_10m1_15m1_30p1 : gamma0CuspForms 180 :=
  etaQuotientCuspForm 180 sparse![180; 0 => -3, 1 => 5, 2 => 1, 4 => 3, 5 => -1, 9 => -1, 14 => -1, 29 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_180_eta_1m3_2p5_3p1_5p3_6m1_10m1_15m1_30p1_first_coeffs :
    first_coeffs 100 cuspForm_180_eta_1m3_2p5_3p1_5p3_6m1_10m1_15m1_30p1 =
    [0, 1, 3, 4, 6, 8, 6, 5, 6, 4, 3, 6, 3, -1, 0, -1, 0, 0, 3, 2,
     -3, -4, -3, -3, -6, 1, -6, -8, -9, -9, -3, -10, -3, -6, -12, -26, -12, -7, -15, 2,
     -3, -9, -18, -4, -6, -7, 0, 0, -9, -15, 3, 6, -3, 0, 6, -3, 0, -4, 12, 0,
     12, 8, 0, 2, -6, 13, -6, 14, 3, 6, -9, 0, 15, 8, 24, 4, 6, 9, 6, 2,
     0, 10, 21, 6, 18, 12, 12, -6, 21, 21, -6, 10, 0, 8, 6, 55, 30, 2, 6, 6] := by
  eta_coeff

end WeightTwoCusps
