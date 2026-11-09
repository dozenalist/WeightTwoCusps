module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 340

The eta expression is `η(z)^(-4) η(2z)^10 η(4z)^(-4) η(5z) η(10z)^(-2) η(17z) η(20z) η(34z)^(-2) η(68z) η(85z)^(-2) η(170z)^6 η(340z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^10 η(4z)^(-4) η(5z) η(10z)^(-2) η(17z) η(20z) η(34z)^(-2) η(68z) η(85z)^(-2) η(170z)^6 η(340z)^(-2)` at level 340. -/
abbrev cuspForm_340_eta_1m4_2p10_4m4_5p1_10m2_17p1_20p1_34m2_68p1_85m2_170p6_340m2 : gamma0CuspForms 340 :=
  etaQuotientCuspForm 340 sparse![340; 0 => -4, 1 => 10, 3 => -4, 4 => 1, 9 => -2, 16 => 1, 19 => 1, 33 => -2, 67 => 1, 84 => -2, 169 => 6, 339 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_340_eta_1m4_2p10_4m4_5p1_10m2_17p1_20p1_34m2_68p1_85m2_170p6_340m2_first_coeffs :
    first_coeffs 100 cuspForm_340_eta_1m4_2p10_4m4_5p1_10m2_17p1_20p1_34m2_68p1_85m2_170p6_340m2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 4, 0, 4, 7, -4, -4, 4, 0, 1, 4,
     4, 4, 0, -2, -4, -1, -4, -8, 2, 0, -7, 0, 4, -3, 0, -5, -8, 0, -12, 0,
     6, 0, 5, 3, 8, -2, 0, 3, -2, -4, -1, 0, 1, 8, -4, 12, 0, -10, 2, -10,
     -7, -8, -2, -12, -10, 2, 8, 1, -1, -2, -16, 0, -16, -2, 12, 6, 14, 7, 10, -4,
     4, 10, 2, -7, -2, 1, 2, 16, -4, 20, 6, -20, -2, -15, 2, -6, -4, 4, -1, -4] := by
  eta_coeff

end WeightTwoCusps
