module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«208».New.«208_eta_1m1_2p2_4p1_13p1_52p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 416

The eta expression is `η(z)^(-1) η(2z)^2 η(4z) η(13z) η(52z)`; see
[the local level table](../../TABLE.md#level-416).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_208_eta_1m1_2p2_4p1_13p1_52p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(4z) η(13z) η(52z)` at level 416. -/
abbrev cuspForm_208_eta_1m1_2p2_4p1_13p1_52p1_old_416_1 : gamma0CuspForms 416 :=
  gamma0RescaleToLevel cuspForm_208_eta_1m1_2p2_4p1_13p1_52p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_208_eta_1m1_2p2_4p1_13p1_52p1_old_416_1_eq_eta :
    cuspForm_208_eta_1m1_2p2_4p1_13p1_52p1_old_416_1 =
      etaQuotientCuspForm 416 sparse![416; 0 => -1, 1 => 2, 3 => 1, 12 => 1, 51 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_208_eta_1m1_2p2_4p1_13p1_52p1_old_416_1_first_coeffs :
    first_coeffs 100 cuspForm_208_eta_1m1_2p2_4p1_13p1_52p1_old_416_1 =
    [0, 0, 0, 1, 1, 0, 1, -1, -1, 1, -1, -1, -1, 0, -1, 0, -1, -3, 1, -1,
     1, 0, -2, 2, 3, 1, 0, 1, -1, 0, 1, 1, -1, 2, 3, -1, 0, 0, 2, 0,
     1, 2, -1, 1, -2, 0, 0, -1, 3, -1, -3, -1, -1, 0, -1, -2, -1, -4, 0, 1,
     1, -2, 0, -1, -1, 1, -2, 1, 3, 6, -1, 1, -6, -2, 3, -2, -2, -2, 1, 0,
     1, 0, -2, 1, -1, -4, -1, 0, 2, 2, 0, 0, 4, -4, 3, 0, 3, 4, 1, 1] := by
  eta_coeff

end WeightTwoCusps
