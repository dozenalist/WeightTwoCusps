module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«98».New.«98_eta_1p2_2m1_7p1_14p1_49m1_98p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 294

The eta expression is `η(z)^2 η(2z)^(-1) η(7z) η(14z) η(49z)^(-1) η(98z)^2`; see
[the local level table](../../TABLE.md#level-294).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_98_eta_1p2_2m1_7p1_14p1_49m1_98p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^2 η(2z)^(-1) η(7z) η(14z) η(49z)^(-1) η(98z)^2` at level 294. -/
abbrev cuspForm_98_eta_1p2_2m1_7p1_14p1_49m1_98p2_old_294_1 : gamma0CuspForms 294 :=
  gamma0RescaleToLevel cuspForm_98_eta_1p2_2m1_7p1_14p1_49m1_98p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_98_eta_1p2_2m1_7p1_14p1_49m1_98p2_old_294_1_eq_eta :
    cuspForm_98_eta_1p2_2m1_7p1_14p1_49m1_98p2_old_294_1 =
      etaQuotientCuspForm 294 sparse![294; 0 => 2, 1 => -1, 6 => 1, 13 => 1, 48 => -1, 97 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_98_eta_1p2_2m1_7p1_14p1_49m1_98p2_old_294_1_first_coeffs :
    first_coeffs 100 cuspForm_98_eta_1p2_2m1_7p1_14p1_49m1_98p2_old_294_1 =
    [0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0, 2, 0, 0, -1, 2, -2, 0, -2, 0,
     0, -2, 4, 4, 0, -4, 0, 0, 1, -2, 2, 0, 0, 0, 0, 0, 0, -6, 0, 2,
     0, 0, 2, -2, 2, 0, 8, 0, 0, 1, -4, -4, 0, 0, 0, 0, -1, -6, 2, 0,
     2, 0, 0, 1, 4, 0, 0, -6, 0, 0, 0, 10, 4, 0, -10, 0, 0, 0, -2, 6,
     0, 2, 0, 0, -2, 2, -12, 0, -4, 0, 0, -4, 4, 8, 0, 10, 0, 0, -1, -4] := by
  eta_coeff

end WeightTwoCusps
