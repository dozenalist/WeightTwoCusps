module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 416

The eta expression is `η(z)^(-1) η(2z)^3 η(4z)^(-2) η(8z) η(13z) η(16z)^2 η(26z)^(-1) η(32z)^(-1) η(52z)^2 η(104z)^(-1) η(416z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^3 η(4z)^(-2) η(8z) η(13z) η(16z)^2 η(26z)^(-1) η(32z)^(-1) η(52z)^2 η(104z)^(-1) η(416z)` at level 416. -/
abbrev cuspForm_416_eta_1m1_2p3_4m2_8p1_13p1_16p2_26m1_32m1_52p2_104m1_416p1 : gamma0CuspForms 416 :=
  etaQuotientCuspForm 416 sparse![416; 0 => -1, 1 => 3, 3 => -2, 7 => 1, 12 => 1, 15 => 2, 25 => -1, 31 => -1, 51 => 2, 103 => -1, 415 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_416_eta_1m1_2p3_4m2_8p1_13p1_16p2_26m1_32m1_52p2_104m1_416p1_first_coeffs :
    first_coeffs 100 cuspForm_416_eta_1m1_2p3_4m2_8p1_13p1_16p2_26m1_32m1_52p2_104m1_416p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, -1,
     0, 1, 0, -1, -1, 1, 0, -1, -1, 1, 0, -3, 1, -1, -3, 0, 0, 1, 0, 0,
     2, 1, 0, -1, 3, 1, 0, 3, -2, 2, 1, 0, 1, -1, 0, -1, 0, -2, 0, 0,
     -2, 1, 0, 1, 0, -1, 2, 1, -2, -5, 0, 2, 1, 1, 0, 4, 1, -5, 0, 0,
     1, -1, 2, 3, -2, 4, 0, 3, -4, -4, 0, -1, -4, -3, 0, 0, -1, -5, -1, -1] := by
  eta_coeff

end WeightTwoCusps
