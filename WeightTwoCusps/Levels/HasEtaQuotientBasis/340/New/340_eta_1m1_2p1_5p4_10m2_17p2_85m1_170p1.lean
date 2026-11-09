module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 340

The eta expression is `η(z)^(-1) η(2z) η(5z)^4 η(10z)^(-2) η(17z)^2 η(85z)^(-1) η(170z)`; see
[the local level table](../../TABLE.md#level-340).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(5z)^4 η(10z)^(-2) η(17z)^2 η(85z)^(-1) η(170z)` at level 340. -/
abbrev cuspForm_340_eta_1m1_2p1_5p4_10m2_17p2_85m1_170p1 : gamma0CuspForms 340 :=
  etaQuotientCuspForm 340 sparse![340; 0 => -1, 1 => 1, 4 => 4, 9 => -2, 16 => 2, 84 => -1, 169 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_340_eta_1m1_2p1_5p4_10m2_17p2_85m1_170p1_first_coeffs :
    first_coeffs 100 cuspForm_340_eta_1m1_2p1_5p4_10m2_17p2_85m1_170p1 =
    [0, 0, 0, 0, 0, 1, 1, 1, 2, 2, -1, 0, 1, -2, 0, 2, 0, -1, 2, -2,
     -1, 0, -4, -4, -4, -4, -4, 3, 0, 0, 2, -3, -4, -2, 2, -4, 4, 0, 0, 3,
     0, 3, -2, -2, -3, 1, -5, 8, 8, -2, 4, 1, -4, 0, 5, 2, 5, 8, 4, 2,
     6, 1, -1, 0, -6, -1, 4, 4, -2, 12, 0, 0, -2, -5, 6, -4, 6, -2, 5, -5,
     3, -6, -9, 4, -8, -1, -4, 0, -3, -4, 0, -7, 5, 6, 6, -8, 5, 10, -8, 3] := by
  eta_coeff

end WeightTwoCusps
