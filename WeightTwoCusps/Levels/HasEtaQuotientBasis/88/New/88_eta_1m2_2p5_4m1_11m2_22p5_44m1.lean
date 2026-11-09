module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 88

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-1) η(11z)^(-2) η(22z)^5 η(44z)^(-1)`; see
[the local level table](../../TABLE.md#level-88).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-1) η(11z)^(-2) η(22z)^5 η(44z)^(-1)` at level 88. -/
abbrev cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1 : gamma0CuspForms 88 :=
  etaQuotientCuspForm 88 sparse![88; 0 => -2, 1 => 5, 3 => -1, 10 => -2, 21 => 5, 43 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1_first_coeffs :
    first_coeffs 100 cuspForm_88_eta_1m2_2p5_4m1_11m2_22p5_44m1 =
    [0, 0, 1, 2, 0, 0, 1, -2, 0, 0, -3, 0, 0, 2, 2, -2, 0, 2, -2, -2,
     0, -6, -1, 2, 0, -4, -4, 2, 0, 4, -3, 2, 0, -2, 6, -2, 0, 0, 8, 2,
     0, 2, 2, 0, 0, 4, -3, 4, 0, 8, 4, -2, 0, -4, -5, 0, 0, -2, 0, -6,
     0, -4, 5, -4, 0, 2, -1, 2, 0, 8, -6, 2, 0, -6, -1, 0, 0, 2, -4, 0,
     0, -4, 0, 4, 0, -6, -10, -4, 0, -8, 6, -4, 0, -8, 0, 6, 0, 4, -3, 0] := by
  eta_coeff

end WeightTwoCusps
