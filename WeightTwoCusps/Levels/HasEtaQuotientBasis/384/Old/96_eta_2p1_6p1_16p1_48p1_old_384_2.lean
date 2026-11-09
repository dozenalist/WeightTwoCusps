module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«96».New.«96_eta_2p1_6p1_16p1_48p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 384

The eta expression is `η(4z) η(12z) η(32z) η(96z)`; see
[the local level table](../../TABLE.md#level-384).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(2z)` of `cuspForm_96_eta_2p1_6p1_16p1_48p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z) η(12z) η(32z) η(96z)` at level 384. -/
abbrev cuspForm_96_eta_2p1_6p1_16p1_48p1_old_384_2 : gamma0CuspForms 384 :=
  gamma0RescaleToLevel cuspForm_96_eta_2p1_6p1_16p1_48p1 2 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_96_eta_2p1_6p1_16p1_48p1_old_384_2_eq_eta :
    cuspForm_96_eta_2p1_6p1_16p1_48p1_old_384_2 =
      etaQuotientCuspForm 384 sparse![384; 3 => 1, 11 => 1, 31 => 1, 95 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_96_eta_2p1_6p1_16p1_48p1_old_384_2_first_coeffs :
    first_coeffs 100 cuspForm_96_eta_2p1_6p1_16p1_48p1_old_384_2 =
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, -1, 0,
     0, 0, 1, 0, 0, 0, 2, 0, 0, 0, -1, 0, 0, 0, 2, 0, 0, 0, -1, 0,
     0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, -3, 0,
     0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 4, 0,
     0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, -4, 0] := by
  eta_coeff

end WeightTwoCusps
