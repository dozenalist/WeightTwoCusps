module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 80

The eta expression is `η(z)^(-1) η(2z) η(4z)^2 η(5z) η(10z)`; see
[the local level table](../../TABLE.md#level-80).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(4z)^2 η(5z) η(10z)` at level 80. -/
abbrev cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1 : gamma0CuspForms 80 :=
  etaQuotientCuspForm 80 sparse![80; 0 => -1, 1 => 1, 3 => 2, 4 => 1, 9 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1_first_coeffs :
    first_coeffs 100 cuspForm_80_eta_1m1_2p1_4p2_5p1_10p1 =
    [0, 1, 1, 1, 2, 0, 0, 1, 0, -1, 1, -2, -4, 0, -4, -1, 0, -2, -3, 0,
     -2, -2, 4, -5, 0, 1, -2, -2, 4, 2, 0, 6, 0, 0, 2, 3, 2, 4, 4, 2,
     0, 0, 0, 9, 0, -2, 4, 1, 0, 3, 1, -6, 4, 0, 0, -2, 0, 4, -2, -4,
     4, 0, -8, -7, 0, -2, 0, -5, -12, -6, -4, 6, 0, -2, 6, 1, -8, -8, 0, -4,
     0, -1, -6, 5, -8, 4, -8, 6, 0, -6, -3, -6, 12, 4, 4, -4, 0, -6, 9, 6] := by
  eta_coeff

end WeightTwoCusps
