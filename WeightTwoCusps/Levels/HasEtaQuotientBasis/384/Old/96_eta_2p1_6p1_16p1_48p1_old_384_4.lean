module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«96».New.«96_eta_2p1_6p1_16p1_48p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 384

The eta expression is `η(8z) η(24z) η(64z) η(192z)`; see
[the local level table](../../TABLE.md#level-384).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_96_eta_2p1_6p1_16p1_48p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(8z) η(24z) η(64z) η(192z)` at level 384. -/
abbrev cuspForm_96_eta_2p1_6p1_16p1_48p1_old_384_4 : gamma0CuspForms 384 :=
  gamma0Rescale cuspForm_96_eta_2p1_6p1_16p1_48p1 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_96_eta_2p1_6p1_16p1_48p1_old_384_4_eq_eta :
    cuspForm_96_eta_2p1_6p1_16p1_48p1_old_384_4 =
      etaQuotientCuspForm 384 sparse![384; 7 => 1, 23 => 1, 63 => 1, 191 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_96_eta_2p1_6p1_16p1_48p1_old_384_4_first_coeffs :
    first_coeffs 100 cuspForm_96_eta_2p1_6p1_16p1_48p1_old_384_4 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
     -1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0,
     -1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
