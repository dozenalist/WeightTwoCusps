module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«76».New.«76_eta_1m3_2p8_4m3_19p1_76p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 456

The eta expression is `η(z)^(-3) η(2z)^8 η(4z)^(-3) η(19z) η(76z)`; see
[the local level table](../../TABLE.md#level-456).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_76_eta_1m3_2p8_4m3_19p1_76p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^8 η(4z)^(-3) η(19z) η(76z)` at level 456. -/
abbrev cuspForm_76_eta_1m3_2p8_4m3_19p1_76p1_old_456_1 : gamma0CuspForms 456 :=
  gamma0RescaleToLevel cuspForm_76_eta_1m3_2p8_4m3_19p1_76p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_76_eta_1m3_2p8_4m3_19p1_76p1_old_456_1_eq_eta :
    cuspForm_76_eta_1m3_2p8_4m3_19p1_76p1_old_456_1 =
      etaQuotientCuspForm 456 sparse![456; 0 => -3, 1 => 8, 3 => -3, 18 => 1, 75 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_76_eta_1m3_2p8_4m3_19p1_76p1_old_456_1_first_coeffs :
    first_coeffs 100 cuspForm_76_eta_1m3_2p8_4m3_19p1_76p1_old_456_1 =
    [0, 0, 0, 0, 1, 3, 1, -2, 2, 1, -4, -1, -2, 0, 2, -4, -1, -2, -2, 1,
     0, 2, -2, 1, -3, -5, 3, -2, 1, 6, 6, 2, -2, -2, 4, 5, 0, 2, -1, 3,
     2, 2, -3, -1, 4, -3, 0, -5, 2, -4, 2, 4, -4, 4, -1, 7, 0, -1, -5, -8,
     -2, -3, -2, 3, 3, -6, 2, -2, -1, 0, -4, 0, 0, -8, -2, 2, 0, -3, -4, 6,
     -6, -4, 0, 6, 0, 3, 4, -5, 4, 2, 2, 2, -1, -2, 6, -1, 5, 2, 4, 5] := by
  eta_coeff

end WeightTwoCusps
