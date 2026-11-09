module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«104».New.«104_eta_1p1_2m2_4p4_8m1_13m1_26p4_52m2_104p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 416

The eta expression is `η(4z) η(8z)^(-2) η(16z)^4 η(32z)^(-1) η(52z)^(-1) η(104z)^4 η(208z)^(-2) η(416z)`; see
[the local level table](../../TABLE.md#level-416).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_104_eta_1p1_2m2_4p4_8m1_13m1_26p4_52m2_104p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z) η(8z)^(-2) η(16z)^4 η(32z)^(-1) η(52z)^(-1) η(104z)^4 η(208z)^(-2) η(416z)` at level 416. -/
abbrev cuspForm_104_eta_1p1_2m2_4p4_8m1_13m1_26p4_52m2_104p1_old_416_4 : gamma0CuspForms 416 :=
  gamma0Rescale cuspForm_104_eta_1p1_2m2_4p4_8m1_13m1_26p4_52m2_104p1 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_104_eta_1p1_2m2_4p4_8m1_13m1_26p4_52m2_104p1_old_416_4_eq_eta :
    cuspForm_104_eta_1p1_2m2_4p4_8m1_13m1_26p4_52m2_104p1_old_416_4 =
      etaQuotientCuspForm 416 sparse![416; 3 => 1, 7 => -2, 15 => 4, 31 => -1, 51 => -1, 103 => 4, 207 => -2, 415 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_104_eta_1p1_2m2_4p4_8m1_13m1_26p4_52m2_104p1_old_416_4_first_coeffs :
    first_coeffs 100 cuspForm_104_eta_1p1_2m2_4p4_8m1_13m1_26p4_52m2_104p1_old_416_4 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
     -1, 0, 0, 0, 1, 0, 0, 0, -2, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, -3, 0, 0, 0, 1, 0, 0, 0,
     -3, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, -1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
