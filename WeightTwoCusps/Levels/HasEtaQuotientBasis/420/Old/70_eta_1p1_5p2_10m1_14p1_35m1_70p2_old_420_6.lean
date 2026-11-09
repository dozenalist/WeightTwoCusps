module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«70».New.«70_eta_1p1_5p2_10m1_14p1_35m1_70p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(6z) η(30z)^2 η(60z)^(-1) η(84z) η(210z)^(-1) η(420z)^2`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(6z)` of `cuspForm_70_eta_1p1_5p2_10m1_14p1_35m1_70p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z) η(30z)^2 η(60z)^(-1) η(84z) η(210z)^(-1) η(420z)^2` at level 420. -/
abbrev cuspForm_70_eta_1p1_5p2_10m1_14p1_35m1_70p2_old_420_6 : gamma0CuspForms 420 :=
  gamma0Rescale cuspForm_70_eta_1p1_5p2_10m1_14p1_35m1_70p2 6

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_70_eta_1p1_5p2_10m1_14p1_35m1_70p2_old_420_6_eq_eta :
    cuspForm_70_eta_1p1_5p2_10m1_14p1_35m1_70p2_old_420_6 =
      etaQuotientCuspForm 420 sparse![420; 5 => 1, 29 => 2, 59 => -1, 83 => 1, 209 => -1, 419 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_70_eta_1p1_5p2_10m1_14p1_35m1_70p2_old_420_6_first_coeffs :
    first_coeffs 100 cuspForm_70_eta_1p1_5p2_10m1_14p1_35m1_70p2_old_420_6 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     -1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
