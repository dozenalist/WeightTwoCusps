module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«81».New.«81_eta_3m1_9p6_27m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 324

The eta expression is `η(12z)^(-1) η(36z)^6 η(108z)^(-1)`; see
[the local level table](../../TABLE.md#level-324).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_81_eta_3m1_9p6_27m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(12z)^(-1) η(36z)^6 η(108z)^(-1)` at level 324. -/
abbrev cuspForm_81_eta_3m1_9p6_27m1_old_324_4 : gamma0CuspForms 324 :=
  gamma0Rescale cuspForm_81_eta_3m1_9p6_27m1 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_81_eta_3m1_9p6_27m1_old_324_4_eq_eta :
    cuspForm_81_eta_3m1_9p6_27m1_old_324_4 =
      etaQuotientCuspForm 324 sparse![324; 11 => -1, 35 => 6, 107 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_81_eta_3m1_9p6_27m1_old_324_4_first_coeffs :
    first_coeffs 100 cuspForm_81_eta_3m1_9p6_27m1_old_324_4 =
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, -5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, -6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
