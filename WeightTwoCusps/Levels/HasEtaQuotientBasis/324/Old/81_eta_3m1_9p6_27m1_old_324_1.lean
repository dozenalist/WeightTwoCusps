module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«81».New.«81_eta_3m1_9p6_27m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 324

The eta expression is `η(3z)^(-1) η(9z)^6 η(27z)^(-1)`; see
[the local level table](../../TABLE.md#level-324).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_81_eta_3m1_9p6_27m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-1) η(9z)^6 η(27z)^(-1)` at level 324. -/
abbrev cuspForm_81_eta_3m1_9p6_27m1_old_324_1 : gamma0CuspForms 324 :=
  gamma0RescaleToLevel cuspForm_81_eta_3m1_9p6_27m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_81_eta_3m1_9p6_27m1_old_324_1_eq_eta :
    cuspForm_81_eta_3m1_9p6_27m1_old_324_1 =
      etaQuotientCuspForm 324 sparse![324; 2 => -1, 8 => 6, 26 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_81_eta_3m1_9p6_27m1_old_324_1_first_coeffs :
    first_coeffs 100 cuspForm_81_eta_3m1_9p6_27m1_old_324_1 =
    [0, 1, 0, 0, 1, 0, 0, 2, 0, 0, -3, 0, 0, -1, 0, 0, -5, 0, 0, 2,
     0, 0, -6, 0, 0, -2, 0, 0, 2, 0, 0, 8, 0, 0, 9, 0, 0, -7, 0, 0,
     3, 0, 0, 2, 0, 0, 6, 0, 0, -3, 0, 0, -1, 0, 0, 6, 0, 0, 3, 0,
     0, -7, 0, 0, 1, 0, 0, -10, 0, 0, -6, 0, 0, -7, 0, 0, 2, 0, 0, 2,
     0, 0, -12, 0, 0, -9, 0, 0, 6, 0, 0, -2, 0, 0, 12, 0, 0, 2, 0, 0] := by
  eta_coeff

end WeightTwoCusps
