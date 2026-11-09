module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 448

The eta expression is `η(8z) η(16z) η(32z) η(64z)^(-1) η(112z) η(448z)`; see
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

/-- The cuspidal eta quotient `η(8z) η(16z) η(32z) η(64z)^(-1) η(112z) η(448z)` at level 448. -/
abbrev cuspForm_448_eta_8p1_16p1_32p1_64m1_112p1_448p1 : gamma0CuspForms 448 :=
  etaQuotientCuspForm 448 sparse![448; 7 => 1, 15 => 1, 31 => 1, 63 => -1, 111 => 1, 447 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_448_eta_8p1_16p1_32p1_64m1_112p1_448p1_first_coeffs :
    first_coeffs 100 cuspForm_448_eta_8p1_16p1_32p1_64m1_112p1_448p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, -2,
     0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0,
     0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, -1,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
