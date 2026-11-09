module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«150».New.«150_eta_1m1_2p1_5p3_10m1_15p3_30m1_75m1_150p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 300

The eta expression is `η(z)^(-1) η(2z) η(5z)^3 η(10z)^(-1) η(15z)^3 η(30z)^(-1) η(75z)^(-1) η(150z)`; see
[the local level table](../../TABLE.md#level-300).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_150_eta_1m1_2p1_5p3_10m1_15p3_30m1_75m1_150p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(5z)^3 η(10z)^(-1) η(15z)^3 η(30z)^(-1) η(75z)^(-1) η(150z)` at level 300. -/
abbrev cuspForm_150_eta_1m1_2p1_5p3_10m1_15p3_30m1_75m1_150p1_old_300_1 : gamma0CuspForms 300 :=
  gamma0RescaleToLevel cuspForm_150_eta_1m1_2p1_5p3_10m1_15p3_30m1_75m1_150p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_150_eta_1m1_2p1_5p3_10m1_15p3_30m1_75m1_150p1_old_300_1_eq_eta :
    cuspForm_150_eta_1m1_2p1_5p3_10m1_15p3_30m1_75m1_150p1_old_300_1 =
      etaQuotientCuspForm 300 sparse![300; 0 => -1, 1 => 1, 4 => 3, 9 => -1, 14 => 3, 29 => -1, 74 => -1, 149 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_150_eta_1m1_2p1_5p3_10m1_15p3_30m1_75m1_150p1_old_300_1_first_coeffs :
    first_coeffs 100 cuspForm_150_eta_1m1_2p1_5p3_10m1_15p3_30m1_75m1_150p1_old_300_1 =
    [0, 0, 0, 0, 1, 1, 1, 2, 2, 0, 1, 2, 0, 2, 2, 1, 1, 2, 0, -1,
     -1, -3, -4, -6, 1, -1, -4, 0, -4, -4, -3, -1, -4, 2, -4, -4, 1, -4, 4, -3,
     -3, -2, 2, -2, -4, 1, -2, -2, -6, 3, 3, 2, 8, 0, 1, 0, 0, -6, 0, 10,
     3, -3, 2, 2, 3, 2, 2, 2, 2, 4, 4, 12, 2, 12, -2, -1, 6, 6, 4, 2,
     7, 0, 8, 2, -4, 6, 2, 6, 4, 2, 1, 5, 6, 4, 2, -4, -5, -14, -6, 2] := by
  eta_coeff

end WeightTwoCusps
