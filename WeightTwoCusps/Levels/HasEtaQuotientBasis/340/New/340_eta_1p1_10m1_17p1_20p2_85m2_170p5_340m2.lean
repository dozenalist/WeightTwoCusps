module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 340

The eta expression is `η(z) η(10z)^(-1) η(17z) η(20z)^2 η(85z)^(-2) η(170z)^5 η(340z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z) η(10z)^(-1) η(17z) η(20z)^2 η(85z)^(-2) η(170z)^5 η(340z)^(-2)` at level 340. -/
abbrev cuspForm_340_eta_1p1_10m1_17p1_20p2_85m2_170p5_340m2 : gamma0CuspForms 340 :=
  etaQuotientCuspForm 340 sparse![340; 0 => 1, 9 => -1, 16 => 1, 19 => 2, 84 => -2, 169 => 5, 339 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_340_eta_1p1_10m1_17p1_20p2_85m2_170p5_340m2_first_coeffs :
    first_coeffs 100 cuspForm_340_eta_1p1_10m1_17p1_20p2_85m2_170p5_340m2 =
    [0, 0, 1, -1, -1, 0, 0, 1, 0, 1, 0, 0, 1, -1, -2, 0, 0, 0, 0, 0,
     1, 1, 0, 0, -1, 0, -1, -1, 1, -1, 1, 2, 1, -1, 0, 0, -2, 1, 2, 1,
     0, -1, -1, -1, 0, -1, -1, -1, 2, -1, 1, 0, -1, 0, 1, -1, -1, 0, 1, 2,
     0, 2, 0, 0, 1, 0, -1, 1, 0, 3, -1, -1, -3, -1, -1, -1, 0, -1, 1, -2,
     0, 3, -1, 1, 1, 0, -1, 2, -3, -1, 0, 1, 2, -1, 5, 0, 0, 2, -2, -5] := by
  eta_coeff

end WeightTwoCusps
