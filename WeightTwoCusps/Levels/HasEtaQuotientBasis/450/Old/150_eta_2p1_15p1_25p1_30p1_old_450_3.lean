module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«150».New.«150_eta_2p1_15p1_25p1_30p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 450

The eta expression is `η(6z) η(45z) η(75z) η(90z)`; see
[the local level table](../../TABLE.md#level-450).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_150_eta_2p1_15p1_25p1_30p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(6z) η(45z) η(75z) η(90z)` at level 450. -/
abbrev cuspForm_150_eta_2p1_15p1_25p1_30p1_old_450_3 : gamma0CuspForms 450 :=
  gamma0Rescale cuspForm_150_eta_2p1_15p1_25p1_30p1 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_150_eta_2p1_15p1_25p1_30p1_old_450_3_eq_eta :
    cuspForm_150_eta_2p1_15p1_25p1_30p1_old_450_3 =
      etaQuotientCuspForm 450 sparse![450; 5 => 1, 44 => 1, 74 => 1, 89 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_150_eta_2p1_15p1_25p1_30p1_old_450_3_first_coeffs :
    first_coeffs 100 cuspForm_150_eta_2p1_15p1_25p1_30p1_old_450_3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0,
     0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, -1, 0, 0, -2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -3] := by
  eta_coeff

end WeightTwoCusps
