module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 416

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(16z)^2 η(32z)^(-1) η(104z)^3 η(208z)^(-2) η(416z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(16z)^2 η(32z)^(-1) η(104z)^3 η(208z)^(-2) η(416z)` at level 416. -/
abbrev cuspForm_416_eta_1m2_2p5_4m2_16p2_32m1_104p3_208m2_416p1 : gamma0CuspForms 416 :=
  etaQuotientCuspForm 416 sparse![416; 0 => -2, 1 => 5, 3 => -2, 15 => 2, 31 => -1, 103 => 3, 207 => -2, 415 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_416_eta_1m2_2p5_4m2_16p2_32m1_104p3_208m2_416p1_first_coeffs :
    first_coeffs 100 cuspForm_416_eta_1m2_2p5_4m2_16p2_32m1_104p3_208m2_416p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0,
     0, 0, 2, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, -4, 0, 0, 0, 0, -2, 0,
     0, 0, 0, 0, 0, -4, 0, 0, 0, 2, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0,
     0, 0, 2, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0,
     0, 4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
