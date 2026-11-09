module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 416

The eta expression is `η(z) η(2z)^(-1) η(4z)^2 η(8z)^(-1) η(13z)^(-1) η(26z)^3 η(32z) η(52z)^(-2) η(104z) η(208z)^2 η(416z)^(-1)`; see
[the local level table](../../TABLE.md#level-416).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(2z)^(-1) η(4z)^2 η(8z)^(-1) η(13z)^(-1) η(26z)^3 η(32z) η(52z)^(-2) η(104z) η(208z)^2 η(416z)^(-1)` at level 416. -/
abbrev cuspForm_416_eta_1p1_2m1_4p2_8m1_13m1_26p3_32p1_52m2_104p1_208p2_416m1 : gamma0CuspForms 416 :=
  etaQuotientCuspForm 416 sparse![416; 0 => 1, 1 => -1, 3 => 2, 7 => -1, 12 => -1, 25 => 3, 31 => 1, 51 => -2, 103 => 1, 207 => 2, 415 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_416_eta_1p1_2m1_4p2_8m1_13m1_26p3_32p1_52m2_104p1_208p2_416m1_first_coeffs :
    first_coeffs 100 cuspForm_416_eta_1p1_2m1_4p2_8m1_13m1_26p3_32p1_52m2_104p1_208p2_416m1 =
    [0, 0, 0, 0, 1, -1, 0, -1, -1, 1, 1, 1, 0, 0, 0, 0, -1, 2, -2, 0,
     0, -2, 0, 1, 0, 0, 0, 1, 1, -1, 0, 0, 0, 3, 0, -2, -1, -2, 0, 0,
     1, 1, 1, -1, 1, -1, 0, 0, 1, -1, 2, 0, 0, -1, 0, -1, 1, 0, 0, -3,
     -2, 1, 0, 2, -1, 0, 0, 2, -2, 1, 0, 3, 1, -1, -3, 0, -1, -1, 0, 2,
     2, 1, 0, 0, 0, 5, 0, -3, -2, 0, 0, 0, 0, -1, 0, -2, 2, -3, 0, 2] := by
  eta_coeff

end WeightTwoCusps
