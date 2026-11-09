module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«176».New.«176_eta_2p1_8p1_22p1_88p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 352

The eta expression is `η(2z) η(8z) η(22z) η(88z)`; see
[the local level table](../../TABLE.md#level-352).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_176_eta_2p1_8p1_22p1_88p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(8z) η(22z) η(88z)` at level 352. -/
abbrev cuspForm_176_eta_2p1_8p1_22p1_88p1_old_352_1 : gamma0CuspForms 352 :=
  gamma0RescaleToLevel cuspForm_176_eta_2p1_8p1_22p1_88p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_176_eta_2p1_8p1_22p1_88p1_old_352_1_eq_eta :
    cuspForm_176_eta_2p1_8p1_22p1_88p1_old_352_1 =
      etaQuotientCuspForm 352 sparse![352; 1 => 1, 7 => 1, 21 => 1, 87 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_176_eta_2p1_8p1_22p1_88p1_old_352_1_first_coeffs :
    first_coeffs 100 cuspForm_176_eta_2p1_8p1_22p1_88p1_old_352_1 =
    [0, 0, 0, 0, 0, 1, 0, -1, 0, -1, 0, 0, 0, -1, 0, 2, 0, 1, 0, 1,
     0, -1, 0, 0, 0, 1, 0, -2, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, -1,
     0, -1, 0, 2, 0, 2, 0, -2, 0, 0, 0, 3, 0, 2, 0, 1, 0, 3, 0, -2,
     0, 0, 0, -2, 0, -3, 0, -2, 0, -1, 0, 2, 0, -1, 0, 0, 0, -1, 0, 2,
     0, -2, 0, 0, 0, -1, 0, 2, 0, -1, 0, 2, 0, -1, 0, 1, 0, 3, 0, -1] := by
  eta_coeff

end WeightTwoCusps
