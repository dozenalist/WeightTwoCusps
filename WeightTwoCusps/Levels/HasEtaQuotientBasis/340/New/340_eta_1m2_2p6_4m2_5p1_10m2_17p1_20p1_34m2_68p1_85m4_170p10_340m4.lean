module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 340

The eta expression is `η(z)^(-2) η(2z)^6 η(4z)^(-2) η(5z) η(10z)^(-2) η(17z) η(20z) η(34z)^(-2) η(68z) η(85z)^(-4) η(170z)^10 η(340z)^(-4)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^6 η(4z)^(-2) η(5z) η(10z)^(-2) η(17z) η(20z) η(34z)^(-2) η(68z) η(85z)^(-4) η(170z)^10 η(340z)^(-4)` at level 340. -/
abbrev cuspForm_340_eta_1m2_2p6_4m2_5p1_10m2_17p1_20p1_34m2_68p1_85m4_170p10_340m4 : gamma0CuspForms 340 :=
  etaQuotientCuspForm 340 sparse![340; 0 => -2, 1 => 6, 3 => -2, 4 => 1, 9 => -2, 16 => 1, 19 => 1, 33 => -2, 67 => 1, 84 => -4, 169 => 10, 339 => -4]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_340_eta_1m2_2p6_4m2_5p1_10m2_17p1_20p1_34m2_68p1_85m4_170p10_340m4_first_coeffs :
    first_coeffs 100 cuspForm_340_eta_1m2_2p6_4m2_5p1_10m2_17p1_20p1_34m2_68p1_85m4_170p10_340m4 =
    [0, 1, 2, -1, -2, 1, -3, -4, 1, 0, 1, 4, 4, -1, -2, 2, -3, -4, 1, 2,
     0, 5, 5, 1, 4, -3, -5, -7, -3, -2, -3, 9, 4, 1, 0, -2, -9, -8, -2, -3,
     -1, 1, 11, 3, 5, 6, -3, -7, -5, 4, -2, 8, 11, 4, 7, 5, -9, -6, 6, -8,
     -4, 5, 2, -5, 2, 10, -17, -11, 0, -11, -7, 4, 6, -1, 2, -5, -2, -7, 7, 5,
     -3, 18, 1, 5, 5, 3, -1, 4, 6, -7, -3, 3, 10, -11, -1, 2, -11, -4, -5, -5] := by
  eta_coeff

end WeightTwoCusps
