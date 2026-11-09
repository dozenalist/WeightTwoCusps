module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«88».New.«88_eta_2p1_4p1_22p1_44p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 352

The eta expression is `η(2z) η(4z) η(22z) η(44z)`; see
[the local level table](../../TABLE.md#level-352).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_88_eta_2p1_4p1_22p1_44p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(4z) η(22z) η(44z)` at level 352. -/
abbrev cuspForm_88_eta_2p1_4p1_22p1_44p1_old_352_1 : gamma0CuspForms 352 :=
  gamma0RescaleToLevel cuspForm_88_eta_2p1_4p1_22p1_44p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_88_eta_2p1_4p1_22p1_44p1_old_352_1_eq_eta :
    cuspForm_88_eta_2p1_4p1_22p1_44p1_old_352_1 =
      etaQuotientCuspForm 352 sparse![352; 1 => 1, 3 => 1, 21 => 1, 43 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_88_eta_2p1_4p1_22p1_44p1_old_352_1_first_coeffs :
    first_coeffs 100 cuspForm_88_eta_2p1_4p1_22p1_44p1_old_352_1 =
    [0, 0, 0, 1, 0, -1, 0, -2, 0, 1, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0,
     0, -2, 0, 1, 0, -3, 0, -1, 0, 2, 0, 1, 0, -1, 0, -2, 0, 1, 0, 0,
     0, 2, 0, 2, 0, 0, 0, 0, 0, 4, 0, 2, 0, -4, 0, 1, 0, -4, 0, -5,
     0, -2, 0, -4, 0, 4, 0, -1, 0, 5, 0, 3, 0, -2, 0, 0, 0, 2, 0, 2,
     0, 0, 0, 2, 0, -2, 0, 0, 0, -3, 0, 0, 0, -3, 0, 4, 0, -1, 0, -1] := by
  eta_coeff

end WeightTwoCusps
