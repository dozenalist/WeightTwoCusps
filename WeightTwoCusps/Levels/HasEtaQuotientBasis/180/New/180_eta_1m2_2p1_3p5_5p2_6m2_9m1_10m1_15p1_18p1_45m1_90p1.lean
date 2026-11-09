module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 180

The eta expression is `η(z)^(-2) η(2z) η(3z)^5 η(5z)^2 η(6z)^(-2) η(9z)^(-1) η(10z)^(-1) η(15z) η(18z) η(45z)^(-1) η(90z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^5 η(5z)^2 η(6z)^(-2) η(9z)^(-1) η(10z)^(-1) η(15z) η(18z) η(45z)^(-1) η(90z)` at level 180. -/
abbrev cuspForm_180_eta_1m2_2p1_3p5_5p2_6m2_9m1_10m1_15p1_18p1_45m1_90p1 : gamma0CuspForms 180 :=
  etaQuotientCuspForm 180 sparse![180; 0 => -2, 1 => 1, 2 => 5, 4 => 2, 5 => -2, 8 => -1, 9 => -1, 14 => 1, 17 => 1, 44 => -1, 89 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_180_eta_1m2_2p1_3p5_5p2_6m2_9m1_10m1_15p1_18p1_45m1_90p1_first_coeffs :
    first_coeffs 100 cuspForm_180_eta_1m2_2p1_3p5_5p2_6m2_9m1_10m1_15p1_18p1_45m1_90p1 =
    [0, 0, 0, 1, 2, 4, 3, 4, 2, 3, 0, 2, 3, 4, 2, 1, 4, 2, 1, -2,
     -2, -4, -8, -4, -5, 0, -2, -3, -4, -4, -1, -8, -4, -4, -2, -12, -7, 0, -2, -2,
     2, -6, -8, -16, 2, -5, 0, 2, -5, -6, 0, 10, 0, 6, 3, -2, 2, 4, 20, -6,
     7, 8, -4, 4, 6, 8, -4, 4, 2, -4, -10, 8, 9, 4, 6, 1, -18, 2, 2, 8,
     0, -1, 8, -6, 8, 14, 4, -10, -16, 6, -3, 14, 0, 8, -2, 22, 19, 0, -2, 4] := by
  eta_coeff

end WeightTwoCusps
