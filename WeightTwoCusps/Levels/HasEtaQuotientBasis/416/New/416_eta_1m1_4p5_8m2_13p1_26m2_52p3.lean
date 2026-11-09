module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 416

The eta expression is `η(z)^(-1) η(4z)^5 η(8z)^(-2) η(13z) η(26z)^(-2) η(52z)^3`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(4z)^5 η(8z)^(-2) η(13z) η(26z)^(-2) η(52z)^3` at level 416. -/
abbrev cuspForm_416_eta_1m1_4p5_8m2_13p1_26m2_52p3 : gamma0CuspForms 416 :=
  etaQuotientCuspForm 416 sparse![416; 0 => -1, 3 => 5, 7 => -2, 12 => 1, 25 => -2, 51 => 3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_416_eta_1m1_4p5_8m2_13p1_26m2_52p3_first_coeffs :
    first_coeffs 100 cuspForm_416_eta_1m1_4p5_8m2_13p1_26m2_52p3 =
    [0, 0, 0, 0, 0, 1, 1, 2, 3, 0, 2, 1, 0, 4, 2, 1, 2, 2, -1, 1,
     -1, -3, 2, 2, 1, 0, -1, -2, 3, 0, -2, 1, -1, 4, 5, 0, -2, 1, 4, 1,
     4, 0, 0, 6, 0, 0, -6, -6, 0, 2, -1, -2, -1, -6, -1, 0, -6, -2, 2, 3,
     1, 0, -8, -3, 2, -6, 2, -5, -2, 2, 3, -6, -10, -2, -6, -2, -2, -4, 0, -4,
     -5, -4, -6, 1, 5, 7, -1, 2, -2, -2, -6, 1, 6, -4, 2, -2, -3, -8, -5, -3] := by
  eta_coeff

end WeightTwoCusps
