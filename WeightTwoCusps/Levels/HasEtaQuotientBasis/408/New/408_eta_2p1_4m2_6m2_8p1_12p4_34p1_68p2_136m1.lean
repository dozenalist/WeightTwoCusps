module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 408

The eta expression is `η(2z) η(4z)^(-2) η(6z)^(-2) η(8z) η(12z)^4 η(34z) η(68z)^2 η(136z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(2z) η(4z)^(-2) η(6z)^(-2) η(8z) η(12z)^4 η(34z) η(68z)^2 η(136z)^(-1)` at level 408. -/
abbrev cuspForm_408_eta_2p1_4m2_6m2_8p1_12p4_34p1_68p2_136m1 : gamma0CuspForms 408 :=
  etaQuotientCuspForm 408 sparse![408; 1 => 1, 3 => -2, 5 => -2, 7 => 1, 11 => 4, 33 => 1, 67 => 2, 135 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_408_eta_2p1_4m2_6m2_8p1_12p4_34p1_68p2_136m1_first_coeffs :
    first_coeffs 100 cuspForm_408_eta_2p1_4m2_6m2_8p1_12p4_34p1_68p2_136m1 =
    [0, 0, 0, 1, 0, -1, 0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 0, -2, 0, 1,
     0, 0, 0, 0, 0, -1, 0, 1, 0, -1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 3,
     0, -2, 0, 1, 0, -1, 0, 2, 0, -2, 0, 2, 0, -2, 0, 1, 0, 0, 0, 2,
     0, -1, 0, 2, 0, 0, 0, 2, 0, -1, 0, -3, 0, 0, 0, -1, 0, -2, 0, 2,
     0, 2, 0, 0, 0, 4, 0, -2, 0, -2, 0, 1, 0, 2, 0, -2, 0, 2, 0, 1] := by
  eta_coeff

end WeightTwoCusps
