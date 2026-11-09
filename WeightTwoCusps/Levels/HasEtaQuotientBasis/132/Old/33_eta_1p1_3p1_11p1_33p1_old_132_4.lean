module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«33».New.«33_eta_1p1_3p1_11p1_33p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 132

The eta expression is `η(4z) η(12z) η(44z) η(132z)`; see
[the local level table](../../TABLE.md#level-132).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(4z)` of `cuspForm_33_eta_1p1_3p1_11p1_33p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z) η(12z) η(44z) η(132z)` at level 132. -/
abbrev cuspForm_33_eta_1p1_3p1_11p1_33p1_old_132_4 : gamma0CuspForms 132 :=
  gamma0Rescale cuspForm_33_eta_1p1_3p1_11p1_33p1 4

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_33_eta_1p1_3p1_11p1_33p1_old_132_4_eq_eta :
    cuspForm_33_eta_1p1_3p1_11p1_33p1_old_132_4 =
      etaQuotientCuspForm 132 sparse![132; 3 => 1, 11 => 1, 43 => 1, 131 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_33_eta_1p1_3p1_11p1_33p1_old_132_4_first_coeffs :
    first_coeffs 100 cuspForm_33_eta_1p1_3p1_11p1_33p1_old_132_4 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0,
     -1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, -1, 0, 0, 0, 2, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
