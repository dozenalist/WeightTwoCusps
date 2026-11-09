module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«210».New.«210_eta_1m2_2p3_3p2_5p1_6m1_10m1_70p1_105m1_210p2»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 420

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^2 η(5z) η(6z)^(-1) η(10z)^(-1) η(70z) η(105z)^(-1) η(210z)^2`; see
[the local level table](../../TABLE.md#level-420).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_210_eta_1m2_2p3_3p2_5p1_6m1_10m1_70p1_105m1_210p2`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^2 η(5z) η(6z)^(-1) η(10z)^(-1) η(70z) η(105z)^(-1) η(210z)^2` at level 420. -/
abbrev cuspForm_210_eta_1m2_2p3_3p2_5p1_6m1_10m1_70p1_105m1_210p2_old_420_1 : gamma0CuspForms 420 :=
  gamma0RescaleToLevel cuspForm_210_eta_1m2_2p3_3p2_5p1_6m1_10m1_70p1_105m1_210p2 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_210_eta_1m2_2p3_3p2_5p1_6m1_10m1_70p1_105m1_210p2_old_420_1_eq_eta :
    cuspForm_210_eta_1m2_2p3_3p2_5p1_6m1_10m1_70p1_105m1_210p2_old_420_1 =
      etaQuotientCuspForm 420 sparse![420; 0 => -2, 1 => 3, 2 => 2, 4 => 1, 5 => -1, 9 => -1, 69 => 1, 104 => -1, 209 => 2] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m2_2p3_3p2_5p1_6m1_10m1_70p1_105m1_210p2_old_420_1_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m2_2p3_3p2_5p1_6m1_10m1_70p1_105m1_210p2_old_420_1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 2,
     1, 1, 0, 0, 1, -1, 0, 0, 0, -1, 0, 1, -2, -2, -2, -1, -4, 0, 2, -1,
     1, 0, -2, -4, 0, 1, -3, -2, 0, -2, -1, 2, 2, -4, -1, -1, -3, 2, 2, 2,
     0, 3, -2, -2, -2, 0, -1, -2, 4, -2, 2, 3, 0, 0, 1, -2, -4, 2, 4, 4,
     1, 2, 0, -2, 2, -1, -2, 0, 0, -2, 0, 2, 0, -4, 1, 1, 1, 2, 2, 2] := by
  eta_coeff

end WeightTwoCusps
