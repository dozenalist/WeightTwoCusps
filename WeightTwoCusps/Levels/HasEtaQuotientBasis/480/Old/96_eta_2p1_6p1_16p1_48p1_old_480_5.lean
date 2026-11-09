module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«96».New.«96_eta_2p1_6p1_16p1_48p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 480

The eta expression is `η(10z) η(30z) η(80z) η(240z)`; see
[the local level table](../../TABLE.md#level-480).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(5z)` of `cuspForm_96_eta_2p1_6p1_16p1_48p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(10z) η(30z) η(80z) η(240z)` at level 480. -/
abbrev cuspForm_96_eta_2p1_6p1_16p1_48p1_old_480_5 : gamma0CuspForms 480 :=
  gamma0Rescale cuspForm_96_eta_2p1_6p1_16p1_48p1 5

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_96_eta_2p1_6p1_16p1_48p1_old_480_5_eq_eta :
    cuspForm_96_eta_2p1_6p1_16p1_48p1_old_480_5 =
      etaQuotientCuspForm 480 sparse![480; 9 => 1, 29 => 1, 79 => 1, 239 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_96_eta_2p1_6p1_16p1_48p1_old_480_5_first_coeffs :
    first_coeffs 100 cuspForm_96_eta_2p1_6p1_16p1_48p1_old_480_5 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
     0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0,
     0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
