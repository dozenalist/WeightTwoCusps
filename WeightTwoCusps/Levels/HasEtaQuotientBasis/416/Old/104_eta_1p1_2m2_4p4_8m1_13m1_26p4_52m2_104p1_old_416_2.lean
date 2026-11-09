module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«104».New.«104_eta_1p1_2m2_4p4_8m1_13m1_26p4_52m2_104p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 416

The eta expression is `η(2z) η(4z)^(-2) η(8z)^4 η(16z)^(-1) η(26z)^(-1) η(52z)^4 η(104z)^(-2) η(208z)`; see
[the local level table](../../TABLE.md#level-416).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_104_eta_1p1_2m2_4p4_8m1_13m1_26p4_52m2_104p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(4z)^(-2) η(8z)^4 η(16z)^(-1) η(26z)^(-1) η(52z)^4 η(104z)^(-2) η(208z)` at level 416. -/
abbrev cuspForm_104_eta_1p1_2m2_4p4_8m1_13m1_26p4_52m2_104p1_old_416_2 : gamma0CuspForms 416 :=
  gamma0RescaleToLevel cuspForm_104_eta_1p1_2m2_4p4_8m1_13m1_26p4_52m2_104p1 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_104_eta_1p1_2m2_4p4_8m1_13m1_26p4_52m2_104p1_old_416_2_eq_eta :
    cuspForm_104_eta_1p1_2m2_4p4_8m1_13m1_26p4_52m2_104p1_old_416_2 =
      etaQuotientCuspForm 416 sparse![416; 1 => 1, 3 => -2, 7 => 4, 15 => -1, 25 => -1, 51 => 4, 103 => -2, 207 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_104_eta_1p1_2m2_4p4_8m1_13m1_26p4_52m2_104p1_old_416_2_first_coeffs :
    first_coeffs 100 cuspForm_104_eta_1p1_2m2_4p4_8m1_13m1_26p4_52m2_104p1_old_416_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 1, 0, -2, 0, -1, 0, 0, 0,
     1, 0, 1, 0, 1, 0, 0, 0, -1, 0, 1, 0, 1, 0, 2, 0, -3, 0, 1, 0,
     -3, 0, -1, 0, 0, 0, 2, 0, -1, 0, 0, 0, 0, 0, -2, 0, -1, 0, 4, 0,
     -1, 0, 1, 0, -1, 0, 4, 0, 3, 0, 0, 0, -2, 0, -5, 0, -4, 0, 1, 0,
     3, 0, -4, 0, 1, 0, -2, 0, 6, 0, 0, 0, 4, 0, 2, 0, 1, 0, -6, 0] := by
  eta_coeff

end WeightTwoCusps
