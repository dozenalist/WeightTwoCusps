module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 392

The eta expression is `η(8z) η(14z)^3 η(28z)^(-1) η(98z)^(-1) η(196z)^3 η(392z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(8z) η(14z)^3 η(28z)^(-1) η(98z)^(-1) η(196z)^3 η(392z)^(-1)` at level 392. -/
abbrev cuspForm_392_eta_8p1_14p3_28m1_98m1_196p3_392m1 : gamma0CuspForms 392 :=
  etaQuotientCuspForm 392 sparse![392; 7 => 1, 13 => 3, 27 => -1, 97 => -1, 195 => 3, 391 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_392_eta_8p1_14p3_28m1_98m1_196p3_392m1_first_coeffs :
    first_coeffs 100 cuspForm_392_eta_8p1_14p3_28m1_98m1_196p3_392m1 =
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -3,
     0, -1, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0,
     0, -1, 0, 0, 0, 1, 0, 2, 0, -1, 0, 0, 0, 0, 0, -2, 0, 0, 0, -3,
     0, 3, 0, -2, 0, 0, 0, 0, 0, -2, 0, 0, 0, 1, 0, -4, 0, -2, 0, 0,
     0, 0, 0, 1, 0, 0, 0, 2, 0, -3, 0, 1, 0, 0, 0, 0, 0, 4, 0, 0] := by
  eta_coeff

end WeightTwoCusps
