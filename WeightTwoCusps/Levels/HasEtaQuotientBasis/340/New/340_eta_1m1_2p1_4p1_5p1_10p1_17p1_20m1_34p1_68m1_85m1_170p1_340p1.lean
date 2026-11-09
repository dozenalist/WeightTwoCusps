module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 340

The eta expression is `η(z)^(-1) η(2z) η(4z) η(5z) η(10z) η(17z) η(20z)^(-1) η(34z) η(68z)^(-1) η(85z)^(-1) η(170z) η(340z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(4z) η(5z) η(10z) η(17z) η(20z)^(-1) η(34z) η(68z)^(-1) η(85z)^(-1) η(170z) η(340z)` at level 340. -/
abbrev cuspForm_340_eta_1m1_2p1_4p1_5p1_10p1_17p1_20m1_34p1_68m1_85m1_170p1_340p1 : gamma0CuspForms 340 :=
  etaQuotientCuspForm 340 sparse![340; 0 => -1, 1 => 1, 3 => 1, 4 => 1, 9 => 1, 16 => 1, 19 => -1, 33 => 1, 67 => -1, 84 => -1, 169 => 1, 339 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_340_eta_1m1_2p1_4p1_5p1_10p1_17p1_20m1_34p1_68m1_85m1_170p1_340p1_first_coeffs :
    first_coeffs 100 cuspForm_340_eta_1m1_2p1_4p1_5p1_10p1_17p1_20m1_34p1_68m1_85m1_170p1_340p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1,
     2, 1, 1, 2, 2, 1, 3, 1, 0, 2, 0, 2, 2, 1, -1, 2, -1, -1, 3, -1,
     0, 0, 0, -3, 3, 2, 0, 2, -2, -1, -1, -2, -3, 1, -5, -6, -2, -5, -4, 1,
     -4, -6, 1, -4, 0, -2, -2, -1, 1, -7, -2, 4, -7, 3, -3, -2, -5, 3, -5, -7,
     2, -5, 0, -3, 2, 1, 4, -3, -1, 8, -1, 2, 0, -6, -3, 3, -4, -5, 2, 0] := by
  eta_coeff

end WeightTwoCusps
