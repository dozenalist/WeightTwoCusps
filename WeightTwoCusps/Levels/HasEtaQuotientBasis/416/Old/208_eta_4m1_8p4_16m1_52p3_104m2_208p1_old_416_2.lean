module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«208».New.«208_eta_4m1_8p4_16m1_52p3_104m2_208p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 416

The eta expression is `η(8z)^(-1) η(16z)^4 η(32z)^(-1) η(104z)^3 η(208z)^(-2) η(416z)`; see
[the local level table](../../TABLE.md#level-416).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_208_eta_4m1_8p4_16m1_52p3_104m2_208p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(8z)^(-1) η(16z)^4 η(32z)^(-1) η(104z)^3 η(208z)^(-2) η(416z)` at level 416. -/
abbrev cuspForm_208_eta_4m1_8p4_16m1_52p3_104m2_208p1_old_416_2 : gamma0CuspForms 416 :=
  gamma0Rescale cuspForm_208_eta_4m1_8p4_16m1_52p3_104m2_208p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_208_eta_4m1_8p4_16m1_52p3_104m2_208p1_old_416_2_eq_eta :
    cuspForm_208_eta_4m1_8p4_16m1_52p3_104m2_208p1_old_416_2 =
      etaQuotientCuspForm 416 sparse![416; 7 => -1, 15 => 4, 31 => -1, 103 => 3, 207 => -2, 415 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_208_eta_4m1_8p4_16m1_52p3_104m2_208p1_old_416_2_first_coeffs :
    first_coeffs 100 cuspForm_208_eta_4m1_8p4_16m1_52p3_104m2_208p1_old_416_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
     0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, -1, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0,
     0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
