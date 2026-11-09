module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 340

The eta expression is `η(z)^(-2) η(2z)^4 η(4z)^(-1) η(5z)^2 η(10z)^(-2) η(17z)^2 η(20z) η(34z)^(-2) η(68z) η(85z)^(-2) η(170z)^4 η(340z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(4z)^(-1) η(5z)^2 η(10z)^(-2) η(17z)^2 η(20z) η(34z)^(-2) η(68z) η(85z)^(-2) η(170z)^4 η(340z)^(-1)` at level 340. -/
abbrev cuspForm_340_eta_1m2_2p4_4m1_5p2_10m2_17p2_20p1_34m2_68p1_85m2_170p4_340m1 : gamma0CuspForms 340 :=
  etaQuotientCuspForm 340 sparse![340; 0 => -2, 1 => 4, 3 => -1, 4 => 2, 9 => -2, 16 => 2, 19 => 1, 33 => -2, 67 => 1, 84 => -2, 169 => 4, 339 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_340_eta_1m2_2p4_4m1_5p2_10m2_17p2_20p1_34m2_68p1_85m2_170p4_340m1_first_coeffs :
    first_coeffs 100 cuspForm_340_eta_1m2_2p4_4m1_5p2_10m2_17p2_20p1_34m2_68p1_85m2_170p4_340m1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 2, 3, 0, 0, 2, 0, 0, 4,
     2, 1, 4, 2, 0, 0, 0, -4, -2, -2, -4, 3, 2, -1, 0, 0, -8, -4, -2, -6,
     2, 0, 2, 1, 2, 1, 0, -1, -6, 1, -2, 0, 4, 6, 2, 1, 0, -10, 0, -2,
     -6, 0, 0, -4, -4, 3, -6, -5, 0, -7, -8, -3, 0, -2, 2, 0, 2, -1, -2, 3,
     0, 7, 0, -1, 2, 0, 2, 6, 4, 3, 2, -6, 2, -9, 0, 4, -4, 4, 2, -1] := by
  eta_coeff

end WeightTwoCusps
