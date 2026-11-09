module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 408

The eta expression is `η(4z)^(-1) η(6z) η(8z)^2 η(34z)^(-2) η(68z)^5 η(102z) η(136z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(4z)^(-1) η(6z) η(8z)^2 η(34z)^(-2) η(68z)^5 η(102z) η(136z)^(-2)` at level 408. -/
abbrev cuspForm_408_eta_4m1_6p1_8p2_34m2_68p5_102p1_136m2 : gamma0CuspForms 408 :=
  etaQuotientCuspForm 408 sparse![408; 3 => -1, 5 => 1, 7 => 2, 33 => -2, 67 => 5, 101 => 1, 135 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_408_eta_4m1_6p1_8p2_34m2_68p5_102p1_136m2_first_coeffs :
    first_coeffs 100 cuspForm_408_eta_4m1_6p1_8p2_34m2_68p5_102p1_136m2 =
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0,
     0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3,
     0, -1, 0, 2, 0, -1, 0, 2, 0, -2, 0, 0, 0, 0, 0, -2, 0, -3, 0, 2,
     0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, -1, 0, -2, 0, 2,
     0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, -2, 0, 4, 0, -1, 0, 0, 0, 1] := by
  eta_coeff

end WeightTwoCusps
