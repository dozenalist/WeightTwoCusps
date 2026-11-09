module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«88».New.«88_eta_2p1_4p1_22p1_44p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 352

The eta expression is `η(8z) η(16z) η(88z) η(176z)`; see
[the local level table](../../TABLE.md#level-352).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_88_eta_2p1_4p1_22p1_44p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(8z) η(16z) η(88z) η(176z)` at level 352. -/
abbrev cuspForm_88_eta_2p1_4p1_22p1_44p1_old_352_4 : gamma0CuspForms 352 :=
  gamma0Rescale cuspForm_88_eta_2p1_4p1_22p1_44p1 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_88_eta_2p1_4p1_22p1_44p1_old_352_4_eq_eta :
    cuspForm_88_eta_2p1_4p1_22p1_44p1_old_352_4 =
      etaQuotientCuspForm 352 sparse![352; 7 => 1, 15 => 1, 87 => 1, 175 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_88_eta_2p1_4p1_22p1_44p1_old_352_4_first_coeffs :
    first_coeffs 100 cuspForm_88_eta_2p1_4p1_22p1_44p1_old_352_4 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
     -1, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
