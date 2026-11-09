module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 340

The eta expression is `η(2z)^(-1) η(4z)^2 η(5z) η(17z)^(-2) η(34z)^5 η(68z)^(-2) η(85z)`; see
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

/-- The cuspidal eta quotient `η(2z)^(-1) η(4z)^2 η(5z) η(17z)^(-2) η(34z)^5 η(68z)^(-2) η(85z)` at level 340. -/
abbrev cuspForm_340_eta_2m1_4p2_5p1_17m2_34p5_68m2_85p1 : gamma0CuspForms 340 :=
  etaQuotientCuspForm 340 sparse![340; 1 => -1, 3 => 2, 4 => 1, 16 => -2, 33 => 5, 67 => -2, 84 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_340_eta_2m1_4p2_5p1_17m2_34p5_68m2_85p1_first_coeffs :
    first_coeffs 100 cuspForm_340_eta_2m1_4p2_5p1_17m2_34p5_68m2_85p1 =
    [0, 0, 0, 0, 1, 0, 1, 0, 0, -1, 1, -1, 0, 0, -1, -1, 0, 0, 0, 0,
     -1, 1, 0, 2, 1, 0, -3, 2, -2, 0, 0, -1, -2, 0, 0, 1, 0, -2, -2, 0,
     0, 4, 0, -2, -1, 1, 1, 0, 2, 1, 0, 0, 2, 0, 0, 0, -1, 0, 4, 2,
     1, -2, 2, 2, -1, -1, 1, 0, 0, 1, -2, 1, 2, -2, 2, 0, 4, 0, 2, -3,
     0, -3, -4, -4, -1, 0, 1, -4, 0, -3, 0, -2, 2, 0, -1, 0, -1, 0, -2, 1] := by
  eta_coeff

end WeightTwoCusps
