module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 90

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^2 η(5z) η(6z)^(-1) η(15z)`; see
[the local level table](../../TABLE.md#level-90).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^2 η(5z) η(6z)^(-1) η(15z)` at level 90. -/
abbrev cuspForm_90_eta_1m2_2p3_3p2_5p1_6m1_15p1 : gamma0CuspForms 90 :=
  etaQuotientCuspForm 90 sparse![90; 0 => -2, 1 => 3, 2 => 2, 4 => 1, 5 => -1, 14 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_90_eta_1m2_2p3_3p2_5p1_6m1_15p1_first_coeffs :
    first_coeffs 100 cuspForm_90_eta_1m2_2p3_3p2_5p1_6m1_15p1 =
    [0, 1, 2, 2, 2, 1, 1, 0, 0, 1, -1, -1, -2, -2, -3, -1, -1, -4, -4, -5,
     -1, -6, -2, 0, -3, 1, -1, 2, 0, 4, 4, 0, -2, -2, 1, -3, 5, 8, 2, 2,
     0, 7, 6, 4, 7, -2, 0, 2, 10, 2, 2, 10, -4, 2, 1, 5, -3, -4, 8, -1,
     -5, -2, 6, -6, 4, 1, -10, -6, -8, 0, -3, -2, 0, -8, -11, 2, -1, 0, -8, 0,
     5, 1, -4, -6, -6, -7, 2, -10, -6, -15, -1, -9, 0, 12, -5, -2, -7, 2, -2, 2] := by
  eta_coeff

end WeightTwoCusps
