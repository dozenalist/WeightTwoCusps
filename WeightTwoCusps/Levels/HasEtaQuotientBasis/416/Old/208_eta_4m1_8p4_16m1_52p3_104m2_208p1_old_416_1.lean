module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«208».New.«208_eta_4m1_8p4_16m1_52p3_104m2_208p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 416

The eta expression is `η(4z)^(-1) η(8z)^4 η(16z)^(-1) η(52z)^3 η(104z)^(-2) η(208z)`; see
[the local level table](../../TABLE.md#level-416).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_208_eta_4m1_8p4_16m1_52p3_104m2_208p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^(-1) η(8z)^4 η(16z)^(-1) η(52z)^3 η(104z)^(-2) η(208z)` at level 416. -/
abbrev cuspForm_208_eta_4m1_8p4_16m1_52p3_104m2_208p1_old_416_1 : gamma0CuspForms 416 :=
  gamma0RescaleToLevel cuspForm_208_eta_4m1_8p4_16m1_52p3_104m2_208p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_208_eta_4m1_8p4_16m1_52p3_104m2_208p1_old_416_1_eq_eta :
    cuspForm_208_eta_4m1_8p4_16m1_52p3_104m2_208p1_old_416_1 =
      etaQuotientCuspForm 416 sparse![416; 3 => -1, 7 => 4, 15 => -1, 51 => 3, 103 => -2, 207 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_208_eta_4m1_8p4_16m1_52p3_104m2_208p1_old_416_1_first_coeffs :
    first_coeffs 100 cuspForm_208_eta_4m1_8p4_16m1_52p3_104m2_208p1_old_416_1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, -2, 0, 0, 0, -1,
     0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, -2, 0, 0, 0, -3,
     0, 0, 0, -1, 0, 0, 0, 7, 0, 0, 0, 3, 0, 0, 0, -2, 0, 0, 0, 6,
     0, 0, 0, -5, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -6, 0, 0, 0, -3] := by
  eta_coeff

end WeightTwoCusps
