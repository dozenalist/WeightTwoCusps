module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«208».New.«208_eta_1m1_2p4_4m1_13p1_26m2_52p3»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 416

The eta expression is `η(z)^(-1) η(2z)^4 η(4z)^(-1) η(13z) η(26z)^(-2) η(52z)^3`; see
[the local level table](../../TABLE.md#level-416).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_208_eta_1m1_2p4_4m1_13p1_26m2_52p3`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^4 η(4z)^(-1) η(13z) η(26z)^(-2) η(52z)^3` at level 416. -/
abbrev cuspForm_208_eta_1m1_2p4_4m1_13p1_26m2_52p3_old_416_1 : gamma0CuspForms 416 :=
  gamma0RescaleToLevel cuspForm_208_eta_1m1_2p4_4m1_13p1_26m2_52p3 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_208_eta_1m1_2p4_4m1_13p1_26m2_52p3_old_416_1_eq_eta :
    cuspForm_208_eta_1m1_2p4_4m1_13p1_26m2_52p3_old_416_1 =
      etaQuotientCuspForm 416 sparse![416; 0 => -1, 1 => 4, 3 => -1, 12 => 1, 25 => -2, 51 => 3] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_208_eta_1m1_2p4_4m1_13p1_26m2_52p3_old_416_1_first_coeffs :
    first_coeffs 100 cuspForm_208_eta_1m1_2p4_4m1_13p1_26m2_52p3_old_416_1 =
    [0, 0, 0, 0, 0, 1, 1, -2, -1, 0, -2, 1, 0, 0, 2, 1, 2, -2, -1, 1,
     3, 1, -2, 2, -3, 0, -1, -2, -1, -4, 2, 1, -1, -4, 1, 0, -2, 5, 0, 1,
     4, 4, 4, -2, -4, 0, 6, 2, 0, 6, -5, -2, -1, -6, -5, -8, 2, 2, -2, -5,
     1, 0, -4, 5, 2, 2, 2, 3, 6, 2, -5, -2, 6, -2, 6, 6, -6, 0, 0, -4,
     -5, -4, 2, 9, 1, -9, -5, 2, -10, 2, 2, 1, 6, 0, 10, -2, -3, 0, 11, -3] := by
  eta_coeff

end WeightTwoCusps
