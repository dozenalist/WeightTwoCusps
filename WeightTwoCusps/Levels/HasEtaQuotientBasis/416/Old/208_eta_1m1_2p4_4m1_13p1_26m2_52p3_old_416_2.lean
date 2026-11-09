module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«208».New.«208_eta_1m1_2p4_4m1_13p1_26m2_52p3»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 416

The eta expression is `η(2z)^(-1) η(4z)^4 η(8z)^(-1) η(26z) η(52z)^(-2) η(104z)^3`; see
[the local level table](../../TABLE.md#level-416).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_208_eta_1m1_2p4_4m1_13p1_26m2_52p3`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-1) η(4z)^4 η(8z)^(-1) η(26z) η(52z)^(-2) η(104z)^3` at level 416. -/
abbrev cuspForm_208_eta_1m1_2p4_4m1_13p1_26m2_52p3_old_416_2 : gamma0CuspForms 416 :=
  gamma0Rescale cuspForm_208_eta_1m1_2p4_4m1_13p1_26m2_52p3 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_208_eta_1m1_2p4_4m1_13p1_26m2_52p3_old_416_2_eq_eta :
    cuspForm_208_eta_1m1_2p4_4m1_13p1_26m2_52p3_old_416_2 =
      etaQuotientCuspForm 416 sparse![416; 1 => -1, 3 => 4, 7 => -1, 25 => 1, 51 => -2, 103 => 3] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_208_eta_1m1_2p4_4m1_13p1_26m2_52p3_old_416_2_first_coeffs :
    first_coeffs 100 cuspForm_208_eta_1m1_2p4_4m1_13p1_26m2_52p3_old_416_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, -2, 0, -1, 0, 0, 0,
     -2, 0, 1, 0, 0, 0, 0, 0, 2, 0, 1, 0, 2, 0, -2, 0, -1, 0, 1, 0,
     3, 0, 1, 0, -2, 0, 2, 0, -3, 0, 0, 0, -1, 0, -2, 0, -1, 0, -4, 0,
     2, 0, 1, 0, -1, 0, -4, 0, 1, 0, 0, 0, -2, 0, 5, 0, 0, 0, 1, 0,
     4, 0, 4, 0, 4, 0, -2, 0, -4, 0, 0, 0, 6, 0, 2, 0, 0, 0, 6, 0] := by
  eta_coeff

end WeightTwoCusps
