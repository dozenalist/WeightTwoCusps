module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 180

The eta expression is `η(z)^(-3) η(2z)^6 η(3z)^2 η(4z)^(-2) η(5z) η(6z)^(-2) η(12z) η(60z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^6 η(3z)^2 η(4z)^(-2) η(5z) η(6z)^(-2) η(12z) η(60z)` at level 180. -/
abbrev cuspForm_180_eta_1m3_2p6_3p2_4m2_5p1_6m2_12p1_60p1 : gamma0CuspForms 180 :=
  etaQuotientCuspForm 180 sparse![180; 0 => -3, 1 => 6, 2 => 2, 3 => -2, 4 => 1, 5 => -2, 11 => 1, 59 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_180_eta_1m3_2p6_3p2_4m2_5p1_6m2_12p1_60p1_first_coeffs :
    first_coeffs 100 cuspForm_180_eta_1m3_2p6_3p2_4m2_5p1_6m2_12p1_60p1 =
    [0, 0, 0, 1, 3, 3, 2, 2, 2, 2, 1, 3, 4, 0, -1, -1, -1, -1, 0, 0,
     -1, -2, -2, -1, -6, 0, 1, -3, -2, -5, 0, -4, -4, 0, -2, -8, -6, 0, -2, 2,
     -3, -2, -4, -2, 5, -2, 0, 1, -4, -4, 0, 2, -4, -3, 2, 0, -1, -4, 2, 1,
     6, 4, 2, 0, -5, 3, -4, 2, -4, 2, -2, -4, 8, 0, 3, 1, 8, 6, 0, 0,
     1, 4, 8, 7, 4, 4, -2, -2, 14, 10, -2, 4, 0, 4, 4, 18, 18, 0, 4, 0] := by
  eta_coeff

end WeightTwoCusps
