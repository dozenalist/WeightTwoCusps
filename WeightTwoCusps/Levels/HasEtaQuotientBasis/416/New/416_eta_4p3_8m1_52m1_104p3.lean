module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 416

The eta expression is `η(4z)^3 η(8z)^(-1) η(52z)^(-1) η(104z)^3`; see
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

/-- The cuspidal eta quotient `η(4z)^3 η(8z)^(-1) η(52z)^(-1) η(104z)^3` at level 416. -/
abbrev cuspForm_416_eta_4p3_8m1_52m1_104p3 : gamma0CuspForms 416 :=
  etaQuotientCuspForm 416 sparse![416; 3 => 3, 7 => -1, 51 => -1, 103 => 3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_416_eta_4p3_8m1_52m1_104p3_first_coeffs :
    first_coeffs 100 cuspForm_416_eta_4p3_8m1_52m1_104p3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -3, 0, 0, 0, 1,
     0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, -1, 0, 0, 0, -4, 0, 0, 0, 1,
     0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, -1,
     0, 0, 0, 3, 0, 0, 0, -5, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0,
     0, 0, 0, -3, 0, 0, 0, -6, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 1] := by
  eta_coeff

end WeightTwoCusps
