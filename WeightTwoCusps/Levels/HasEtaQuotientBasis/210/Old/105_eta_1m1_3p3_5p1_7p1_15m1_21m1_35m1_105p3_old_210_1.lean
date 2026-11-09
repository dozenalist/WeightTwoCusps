module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«105».New.«105_eta_1m1_3p3_5p1_7p1_15m1_21m1_35m1_105p3»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 210

The eta expression is `η(z)^(-1) η(3z)^3 η(5z) η(7z) η(15z)^(-1) η(21z)^(-1) η(35z)^(-1) η(105z)^3`; see
[the local level table](../../TABLE.md#level-210).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_105_eta_1m1_3p3_5p1_7p1_15m1_21m1_35m1_105p3`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^3 η(5z) η(7z) η(15z)^(-1) η(21z)^(-1) η(35z)^(-1) η(105z)^3` at level 210. -/
abbrev cuspForm_105_eta_1m1_3p3_5p1_7p1_15m1_21m1_35m1_105p3_old_210_1 : gamma0CuspForms 210 :=
  gamma0RescaleToLevel cuspForm_105_eta_1m1_3p3_5p1_7p1_15m1_21m1_35m1_105p3 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_105_eta_1m1_3p3_5p1_7p1_15m1_21m1_35m1_105p3_old_210_1_eq_eta :
    cuspForm_105_eta_1m1_3p3_5p1_7p1_15m1_21m1_35m1_105p3_old_210_1 =
      etaQuotientCuspForm 210 sparse![210; 0 => -1, 2 => 3, 4 => 1, 6 => 1, 14 => -1, 20 => -1, 34 => -1, 104 => 3] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_105_eta_1m1_3p3_5p1_7p1_15m1_21m1_35m1_105p3_old_210_1_first_coeffs :
    first_coeffs 100 cuspForm_105_eta_1m1_3p3_5p1_7p1_15m1_21m1_35m1_105p3_old_210_1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 2, 0, 1, -3, 0,
     -2, 0, -5, 0, -2, -1, -4, 0, 2, 0, -2, 0, 4, -2, 1, -2, 7, -2, 0, -1,
     4, -5, 0, -1, 7, 2, 0, 5, 1, 1, 1, 0, 0, 2, -1, 3, -4, -2, 4, -2,
     1, 0, 0, -2, -8, -4, 7, -5, -3, 0, 2, 1, -7, -2, 6, -1, 4, 5, 4, 6,
     -2, 1, 5, -3, -3, -5, -7, 1, -5, -1, -3, 4, 4, 0, -11, 4, -4, 0, -1, 2] := by
  eta_coeff

end WeightTwoCusps
