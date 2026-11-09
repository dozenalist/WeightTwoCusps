module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 340

The eta expression is `η(z)^(-1) η(2z) η(5z)^2 η(17z)^4 η(34z)^(-2) η(85z)^(-1) η(170z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(5z)^2 η(17z)^4 η(34z)^(-2) η(85z)^(-1) η(170z)` at level 340. -/
abbrev cuspForm_340_eta_1m1_2p1_5p2_17p4_34m2_85m1_170p1 : gamma0CuspForms 340 :=
  etaQuotientCuspForm 340 sparse![340; 0 => -1, 1 => 1, 4 => 2, 16 => 4, 33 => -2, 84 => -1, 169 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_340_eta_1m1_2p1_5p2_17p4_34m2_85m1_170p1_first_coeffs :
    first_coeffs 100 cuspForm_340_eta_1m1_2p1_5p2_17p4_34m2_85m1_170p1 =
    [0, 0, 0, 0, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 3, 3, 4, 4, 4, 6,
     6, 1, 4, 2, -1, 1, 5, 0, -2, 4, -5, 1, 2, -2, 0, 0, -8, -6, 4, -8,
     3, 4, -4, -4, 3, 0, -7, 6, -6, -7, -1, -8, -4, 6, -2, -8, 5, -12, -8, 2,
     -12, -6, 0, -10, -11, -1, -7, -8, 0, -13, -14, -3, -12, -8, 0, -6, -4, 4, -16, -7,
     7, -3, -6, 6, -3, -4, 5, 2, 2, 11, 3, -12, 4, -14, 1, 10, -7, 8, 6, 3] := by
  eta_coeff

end WeightTwoCusps
