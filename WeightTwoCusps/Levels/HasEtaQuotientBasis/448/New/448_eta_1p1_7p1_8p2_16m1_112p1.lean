module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 448

The eta expression is `η(z) η(7z) η(8z)^2 η(16z)^(-1) η(112z)`; see
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

/-- The cuspidal eta quotient `η(z) η(7z) η(8z)^2 η(16z)^(-1) η(112z)` at level 448. -/
abbrev cuspForm_448_eta_1p1_7p1_8p2_16m1_112p1 : gamma0CuspForms 448 :=
  etaQuotientCuspForm 448 sparse![448; 0 => 1, 6 => 1, 7 => 2, 15 => -1, 111 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_448_eta_1p1_7p1_8p2_16m1_112p1_first_coeffs :
    first_coeffs 100 cuspForm_448_eta_1p1_7p1_8p2_16m1_112p1 =
    [0, 0, 0, 0, 0, 1, -1, -1, 0, 0, 1, 0, 0, -1, 3, 2, 0, -2, -2, -2,
     0, -1, -2, 0, 0, 4, -1, 6, 0, -2, 0, 2, 0, 0, 2, -4, 0, 2, -3, -6,
     0, -2, 1, 0, 0, 1, 4, 2, 0, 0, 2, -4, 0, 4, 2, -6, 0, 0, -2, 6,
     0, 1, -2, 7, 0, 0, 0, -4, 0, -4, -7, 2, 0, -4, -2, -2, 0, 0, 4, 6,
     0, 0, -2, 4, 0, -2, 2, -4, 0, 4, 1, 10, 0, 0, 2, -2, 0, 2, 0, -8] := by
  eta_coeff

end WeightTwoCusps
