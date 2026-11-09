module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 408

The eta expression is `η(z)^2 η(2z)^(-1) η(12z) η(17z)^(-2) η(34z)^5 η(68z)^(-2) η(204z)`; see
[the local level table](../../TABLE.md#level-408).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^2 η(2z)^(-1) η(12z) η(17z)^(-2) η(34z)^5 η(68z)^(-2) η(204z)` at level 408. -/
abbrev cuspForm_408_eta_1p2_2m1_12p1_17m2_34p5_68m2_204p1 : gamma0CuspForms 408 :=
  etaQuotientCuspForm 408 sparse![408; 0 => 2, 1 => -1, 11 => 1, 16 => -2, 33 => 5, 67 => -2, 203 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_408_eta_1p2_2m1_12p1_17m2_34p5_68m2_204p1_first_coeffs :
    first_coeffs 100 cuspForm_408_eta_1p2_2m1_12p1_17m2_34p5_68m2_204p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0, 2, 0, 0, 0, 0, -2, 0,
     0, -1, 2, 0, 0, 0, 2, -4, 0, 0, 6, 0, 0, -1, 0, -4, 0, -4, -2, 4,
     0, 0, 2, 0, 0, 2, 2, 4, 0, -2, -2, 0, 0, 0, -8, 0, 0, -2, 0, 4,
     0, 0, 4, 4, 0, 0, -4, 0, 0, -1, 0, 0, 0, 4, -4, 0, 0, 2, -6, 0,
     0, 4, 2, 0, 0, 0, -6, 0, 0, -2, 10, 0, 0, 1, -4, -4, 0, 0, 4, 4] := by
  eta_coeff

end WeightTwoCusps
