module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 340

The eta expression is `η(z)^(-1) η(2z)^3 η(4z)^(-1) η(10z) η(17z)^(-1) η(34z) η(68z) η(85z)^2 η(170z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^3 η(4z)^(-1) η(10z) η(17z)^(-1) η(34z) η(68z) η(85z)^2 η(170z)^(-1)` at level 340. -/
abbrev cuspForm_340_eta_1m1_2p3_4m1_10p1_17m1_34p1_68p1_85p2_170m1 : gamma0CuspForms 340 :=
  etaQuotientCuspForm 340 sparse![340; 0 => -1, 1 => 3, 3 => -1, 9 => 1, 16 => -1, 33 => 1, 67 => 1, 84 => 2, 169 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_340_eta_1m1_2p3_4m1_10p1_17m1_34p1_68p1_85p2_170m1_first_coeffs :
    first_coeffs 100 cuspForm_340_eta_1m1_2p3_4m1_10p1_17m1_34p1_68p1_85p2_170m1 =
    [0, 0, 0, 0, 1, 1, -1, 0, 0, -1, 0, -1, 0, 0, -1, -1, 0, 0, 0, 2,
     0, 2, 1, -1, -1, -1, 2, 0, -1, 0, 1, 0, -1, 0, 0, 0, 2, 0, 2, 1,
     -2, -1, -1, 2, -1, -1, -1, 1, 0, -2, -1, 0, 0, 2, 2, 3, 1, -3, -1, -3,
     1, -3, -2, -1, 2, 0, -4, -1, 0, 1, 4, 3, 3, 0, -2, 0, -4, 5, -3, -2,
     0, 4, 2, -3, 0, 0, 0, 2, 3, 3, -1, -3, 1, -3, 3, -4, 1, -1, 3, 2] := by
  eta_coeff

end WeightTwoCusps
