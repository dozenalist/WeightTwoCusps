module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 340

The eta expression is `η(4z) η(5z)^(-2) η(10z)^5 η(20z)^(-2) η(68z) η(85z)^2 η(170z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(4z) η(5z)^(-2) η(10z)^5 η(20z)^(-2) η(68z) η(85z)^2 η(170z)^(-1)` at level 340. -/
abbrev cuspForm_340_eta_4p1_5m2_10p5_20m2_68p1_85p2_170m1 : gamma0CuspForms 340 :=
  etaQuotientCuspForm 340 sparse![340; 3 => 1, 4 => -2, 9 => 5, 19 => -2, 67 => 1, 84 => 2, 169 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_340_eta_4p1_5m2_10p5_20m2_68p1_85p2_170m1_first_coeffs :
    first_coeffs 100 cuspForm_340_eta_4p1_5m2_10p5_20m2_68p1_85p2_170m1 =
    [0, 0, 0, 1, 0, 0, 0, -1, 2, 0, 0, -1, -2, 0, 0, 0, -2, 0, 0, 0,
     0, 0, 0, 3, 0, 0, 0, -2, 2, 0, 0, -1, 0, 0, 0, 0, 2, 0, 0, 0,
     0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 1, -2, 0, 0, 0, -4, 0, 0, 0,
     0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 1, 0, 0, 0, 1,
     2, 0, 0, 0, 2, 0, 0, -2, -2, 0, 0, -4, 2, -4, 0, 2, 0, 4, 0, 1] := by
  eta_coeff

end WeightTwoCusps
