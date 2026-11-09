module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«176».New.«176_eta_2p1_8p1_22p1_88p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 352

The eta expression is `η(4z) η(16z) η(44z) η(176z)`; see
[the local level table](../../TABLE.md#level-352).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_176_eta_2p1_8p1_22p1_88p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z) η(16z) η(44z) η(176z)` at level 352. -/
abbrev cuspForm_176_eta_2p1_8p1_22p1_88p1_old_352_2 : gamma0CuspForms 352 :=
  gamma0Rescale cuspForm_176_eta_2p1_8p1_22p1_88p1 2

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_176_eta_2p1_8p1_22p1_88p1_old_352_2_eq_eta :
    cuspForm_176_eta_2p1_8p1_22p1_88p1_old_352_2 =
      etaQuotientCuspForm 352 sparse![352; 3 => 1, 15 => 1, 43 => 1, 175 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_176_eta_2p1_8p1_22p1_88p1_old_352_2_first_coeffs :
    first_coeffs 100 cuspForm_176_eta_2p1_8p1_22p1_88p1_old_352_2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1, 0,
     0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 1, 0,
     0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -2, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, -1, 0,
     0, 0, -1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, -2, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
