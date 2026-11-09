module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 440

The eta expression is `η(2z)^(-1) η(4z) η(10z)^4 η(20z)^(-2) η(22z)^3 η(44z)^(-1)`; see
[the local level table](../../TABLE.md#level-440).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-1) η(4z) η(10z)^4 η(20z)^(-2) η(22z)^3 η(44z)^(-1)` at level 440. -/
abbrev cuspForm_440_eta_2m1_4p1_10p4_20m2_22p3_44m1 : gamma0CuspForms 440 :=
  etaQuotientCuspForm 440 sparse![440; 1 => -1, 3 => 1, 9 => 4, 19 => -2, 21 => 3, 43 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_440_eta_2m1_4p1_10p4_20m2_22p3_44m1_first_coeffs :
    first_coeffs 100 cuspForm_440_eta_2m1_4p1_10p4_20m2_22p3_44m1 =
    [0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, -1, 0, 0, 0, 1, 0, -2, 0, 0,
     0, 2, 0, -3, 0, -4, 0, -1, 0, -8, 0, -7, 0, 3, 0, -2, 0, -5, 0, 4,
     0, 0, 0, -6, 0, 2, 0, 4, 0, -3, 0, 6, 0, 2, 0, -1, 0, 4, 0, 7,
     0, 4, 0, 0, 0, 0, 0, -1, 0, 1, 0, -5, 0, 8, 0, 12, 0, -2, 0, 2,
     0, 1, 0, -6, 0, 2, 0, 12, 0, 3, 0, 0, 0, 17, 0, -4, 0, -3, 0, -2] := by
  eta_coeff

end WeightTwoCusps
