module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«78».New.«78_eta_2p1_3p1_13p1_78p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 234

The eta expression is `η(6z) η(9z) η(39z) η(234z)`; see
[the local level table](../../TABLE.md#level-234).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_78_eta_2p1_3p1_13p1_78p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z) η(9z) η(39z) η(234z)` at level 234. -/
abbrev cuspForm_78_eta_2p1_3p1_13p1_78p1_old_234_3 : gamma0CuspForms 234 :=
  gamma0Rescale cuspForm_78_eta_2p1_3p1_13p1_78p1 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_78_eta_2p1_3p1_13p1_78p1_old_234_3_eq_eta :
    cuspForm_78_eta_2p1_3p1_13p1_78p1_old_234_3 =
      etaQuotientCuspForm 234 sparse![234; 5 => 1, 8 => 1, 38 => 1, 233 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_78_eta_2p1_3p1_13p1_78p1_old_234_3_first_coeffs :
    first_coeffs 100 cuspForm_78_eta_2p1_3p1_13p1_78p1_old_234_3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0,
     0, -1, 0, 0, -1, 0, 0, 1, 0, 0, -1, 0, 0, 1, 0, 0, 1, 0, 0, 0,
     0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 1, 0, 0, 2, 0, 0,
     0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0,
     0, -3, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3] := by
  eta_coeff

end WeightTwoCusps
