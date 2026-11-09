module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 392

The eta expression is `η(2z)^(-2) η(4z)^4 η(8z)^(-1) η(14z)^3 η(28z)^(-1) η(98z) η(196z)^(-1) η(392z)`; see
[the local level table](../../TABLE.md#level-392).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-2) η(4z)^4 η(8z)^(-1) η(14z)^3 η(28z)^(-1) η(98z) η(196z)^(-1) η(392z)` at level 392. -/
abbrev cuspForm_392_eta_2m2_4p4_8m1_14p3_28m1_98p1_196m1_392p1 : gamma0CuspForms 392 :=
  etaQuotientCuspForm 392 sparse![392; 1 => -2, 3 => 4, 7 => -1, 13 => 3, 27 => -1, 97 => 1, 195 => -1, 391 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_392_eta_2m2_4p4_8m1_14p3_28m1_98p1_196m1_392p1_first_coeffs :
    first_coeffs 100 cuspForm_392_eta_2m2_4p4_8m1_14p3_28m1_98p1_196m1_392p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 1, 0, 2,
     0, 3, 0, 2, 0, 4, 0, 1, 0, -2, 0, 3, 0, 1, 0, -1, 0, 2, 0, -2,
     0, 0, 0, 4, 0, -1, 0, -3, 0, -1, 0, 0, 0, -2, 0, 1, 0, -2, 0, -6,
     0, 2, 0, -2, 0, -6, 0, 0, 0, -3, 0, -4, 0, 1, 0, -1, 0, -2, 0, -4,
     0, -2, 0, -5, 0, 0, 0, 2, 0, -7, 0, 5, 0, 0, 0, -2, 0, 0, 0, -6] := by
  eta_coeff

end WeightTwoCusps
