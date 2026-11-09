module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 340

The eta expression is `η(z) η(5z)^(-1) η(10z)^2 η(17z) η(85z)^(-1) η(170z)^2`; see
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

/-- The cuspidal eta quotient `η(z) η(5z)^(-1) η(10z)^2 η(17z) η(85z)^(-1) η(170z)^2` at level 340. -/
abbrev cuspForm_340_eta_1p1_5m1_10p2_17p1_85m1_170p2 : gamma0CuspForms 340 :=
  etaQuotientCuspForm 340 sparse![340; 0 => 1, 4 => -1, 9 => 2, 16 => 1, 84 => -1, 169 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_340_eta_1p1_5m1_10p2_17p1_85m1_170p2_first_coeffs :
    first_coeffs 100 cuspForm_340_eta_1p1_5m1_10p2_17p1_85m1_170p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 0, 0, 2, -1, 0,
     0, 0, 1, 0, 0, 0, 0, 0, -1, -3, 1, 1, 0, 0, 0, 1, 0, 0, 1, -1,
     0, 0, 0, 0, -1, 1, 1, 1, 1, 2, 0, -4, -1, 1, -1, -1, -1, -2, 0, 0,
     0, 1, 1, 2, 0, 0, -2, 0, 0, 4, -1, 1, -1, 0, 2, 0, 0, -2, 2, 0,
     0, 0, -2, -2, 2, -2, 0, -1, 1, -2, 0, 2, 1, 1, 2, -1, 0, 0, -2, 0] := by
  eta_coeff

end WeightTwoCusps
