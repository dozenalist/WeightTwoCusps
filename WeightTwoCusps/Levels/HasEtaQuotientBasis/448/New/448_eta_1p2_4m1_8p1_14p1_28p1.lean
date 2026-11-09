module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 448

The eta expression is `η(z)^2 η(4z)^(-1) η(8z) η(14z) η(28z)`; see
[the local level table](../../TABLE.md#level-448).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^2 η(4z)^(-1) η(8z) η(14z) η(28z)` at level 448. -/
abbrev cuspForm_448_eta_1p2_4m1_8p1_14p1_28p1 : gamma0CuspForms 448 :=
  etaQuotientCuspForm 448 sparse![448; 0 => 2, 3 => -1, 7 => 1, 13 => 1, 27 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_448_eta_1p2_4m1_8p1_14p1_28p1_first_coeffs :
    first_coeffs 100 cuspForm_448_eta_1p2_4m1_8p1_14p1_28p1 =
    [0, 0, 1, -2, -1, 2, 2, 0, -3, 2, 0, -2, -2, 2, 1, -2, -1, 4, 5, -2,
     -4, 0, 4, -6, -2, 2, 4, -4, -1, 4, 0, 0, -3, 0, -2, 0, 3, 0, 6, 2,
     0, 0, -2, 2, -4, -2, -8, -4, 2, 0, -1, 8, 0, 4, -4, 4, 1, -2, 2, 2,
     4, -6, 4, -2, 3, -2, -8, -2, 2, -4, 0, -4, 5, -8, 2, 10, 10, 2, -8, 8,
     0, -10, -2, -2, 2, -8, -4, 8, 8, 4, -8, 4, -4, -4, -4, 2, 6, 0, 1, 6] := by
  eta_coeff

end WeightTwoCusps
