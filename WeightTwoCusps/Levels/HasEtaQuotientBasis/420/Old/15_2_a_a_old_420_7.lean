module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«15».New.«15_2_a_a»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(7z) η(21z) η(35z) η(105z)`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(7z)` of `cuspForm_15_2_a_a`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(7z) η(21z) η(35z) η(105z)` at level 420. -/
abbrev cuspForm_15_2_a_a_old_420_7 : gamma0CuspForms 420 :=
  gamma0RescaleToLevel cuspForm_15_2_a_a 7 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_15_2_a_a_old_420_7_eq_eta :
    cuspForm_15_2_a_a_old_420_7 =
      etaQuotientCuspForm 420 sparse![420; 6 => 1, 20 => 1, 34 => 1, 104 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_15_2_a_a_old_420_7_first_coeffs :
    first_coeffs 100 cuspForm_15_2_a_a_old_420_7 =
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0,
     0, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
     0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0,
     0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -4, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
