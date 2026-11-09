module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 240

The eta expression is `η(z)^(-2) η(2z) η(3z)^4 η(4z) η(5z)^2 η(6z)^(-2) η(10z)^(-1) η(20z)`; see
[the local level table](../../TABLE.md#level-240).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^4 η(4z) η(5z)^2 η(6z)^(-2) η(10z)^(-1) η(20z)` at level 240. -/
abbrev cuspForm_240_eta_1m2_2p1_3p4_4p1_5p2_6m2_10m1_20p1 : gamma0CuspForms 240 :=
  etaQuotientCuspForm 240 sparse![240; 0 => -2, 1 => 1, 2 => 4, 3 => 1, 4 => 2, 5 => -2, 9 => -1, 19 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_240_eta_1m2_2p1_3p4_4p1_5p2_6m2_10m1_20p1_first_coeffs :
    first_coeffs 100 cuspForm_240_eta_1m2_2p1_3p4_4p1_5p2_6m2_10m1_20p1 =
    [0, 1, 2, 4, 4, 5, 4, 4, 4, 5, 6, 4, 4, 2, 4, 4, 8, 6, 2, 0,
     0, 0, 0, 0, 0, -7, -4, 0, 0, -2, -4, -4, -12, -4, -4, -4, -12, -6, 0, -8,
     0, -2, -8, -12, -8, 1, -12, -8, -12, -11, -14, -4, 0, -14, -8, -8, -8, -8, -4, 4,
     -8, -6, 0, -4, -8, -10, 8, -12, 0, -8, -4, 0, 4, 18, -4, -4, 0, 0, -8, 12,
     12, -3, 4, -4, 8, 2, 4, 4, -8, 2, 6, -8, 8, 16, 12, 8, 16, 2, 2, 4] := by
  eta_coeff

end WeightTwoCusps
