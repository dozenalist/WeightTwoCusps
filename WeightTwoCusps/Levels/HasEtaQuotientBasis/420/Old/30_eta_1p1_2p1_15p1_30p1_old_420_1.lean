module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«30».New.«30_eta_1p1_2p1_15p1_30p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(z) η(2z) η(15z) η(30z)`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_30_eta_1p1_2p1_15p1_30p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(2z) η(15z) η(30z)` at level 420. -/
abbrev cuspForm_30_eta_1p1_2p1_15p1_30p1_old_420_1 : gamma0CuspForms 420 :=
  gamma0RescaleToLevel cuspForm_30_eta_1p1_2p1_15p1_30p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_30_eta_1p1_2p1_15p1_30p1_old_420_1_eq_eta :
    cuspForm_30_eta_1p1_2p1_15p1_30p1_old_420_1 =
      etaQuotientCuspForm 420 sparse![420; 0 => 1, 1 => 1, 14 => 1, 29 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_30_eta_1p1_2p1_15p1_30p1_old_420_1_first_coeffs :
    first_coeffs 100 cuspForm_30_eta_1p1_2p1_15p1_30p1_old_420_1 =
    [0, 0, 1, -1, -2, 1, 0, 2, 1, 0, 0, -2, 1, -2, -2, 0, 2, -2, 1, 4,
     -1, 2, -2, 0, 0, 0, 0, -1, 2, 2, -1, -4, -3, 2, 4, -2, -2, -6, 0, 0,
     0, 8, -2, 4, 6, 1, 0, 4, -3, -8, 1, -4, 2, -2, 0, -2, -2, 0, -4, -2,
     2, 4, 4, 2, -2, 0, 2, 8, -6, 0, 2, -4, 1, 4, -4, -1, -4, 0, 2, -4,
     3, 0, 2, 0, 2, 4, 0, 4, -2, -12, 0, 4, 0, -4, 4, 0, 4, 0, 1, -2] := by
  eta_coeff

end WeightTwoCusps
