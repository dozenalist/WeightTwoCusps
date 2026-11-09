module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 340

The eta expression is `η(z) η(2z) η(4z)^(-1) η(5z)^(-1) η(10z) η(17z)^(-1) η(20z) η(34z) η(68z) η(85z) η(170z) η(340z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z) η(2z) η(4z)^(-1) η(5z)^(-1) η(10z) η(17z)^(-1) η(20z) η(34z) η(68z) η(85z) η(170z) η(340z)^(-1)` at level 340. -/
abbrev cuspForm_340_eta_1p1_2p1_4m1_5m1_10p1_17m1_20p1_34p1_68p1_85p1_170p1_340m1 : gamma0CuspForms 340 :=
  etaQuotientCuspForm 340 sparse![340; 0 => 1, 1 => 1, 3 => -1, 4 => -1, 9 => 1, 16 => -1, 19 => 1, 33 => 1, 67 => 1, 84 => 1, 169 => 1, 339 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_340_eta_1p1_2p1_4m1_5m1_10p1_17m1_20p1_34p1_68p1_85p1_170p1_340m1_first_coeffs :
    first_coeffs 100 cuspForm_340_eta_1p1_2p1_4m1_5m1_10p1_17m1_20p1_34p1_68p1_85p1_170p1_340m1 =
    [0, 1, -1, -2, 1, 1, 2, -2, -1, 3, -1, 0, -2, 0, 2, -2, 1, 0, -2, -1,
     -1, 5, 1, 0, 0, 0, 3, -5, -2, 0, 2, 2, -3, 1, 0, -4, 2, -1, 5, 1,
     -1, 2, -4, 1, -5, 1, 2, 0, 0, 0, 0, 0, -3, 1, 1, 6, 4, 1, -2, -5,
     2, -4, 1, -6, 1, 2, -2, -1, 0, -3, 4, 4, 6, 3, -3, 0, -3, -1, -7, -1,
     -1, 8, -2, -3, 2, 0, 0, 3, 3, 4, 0, -2, -2, -8, -1, -3, 6, -1, 1, -4] := by
  eta_coeff

end WeightTwoCusps
