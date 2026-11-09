module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«105».New.«105_eta_1m1_3p1_5p3_7p3_15m1_21m1_35m1_105p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 210

The eta expression is `η(z)^(-1) η(3z) η(5z)^3 η(7z)^3 η(15z)^(-1) η(21z)^(-1) η(35z)^(-1) η(105z)`; see
[the local level table](../../TABLE.md#level-210).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_105_eta_1m1_3p1_5p3_7p3_15m1_21m1_35m1_105p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(3z) η(5z)^3 η(7z)^3 η(15z)^(-1) η(21z)^(-1) η(35z)^(-1) η(105z)` at level 210. -/
abbrev cuspForm_105_eta_1m1_3p1_5p3_7p3_15m1_21m1_35m1_105p1_old_210_1 : gamma0CuspForms 210 :=
  gamma0RescaleToLevel cuspForm_105_eta_1m1_3p1_5p3_7p3_15m1_21m1_35m1_105p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_105_eta_1m1_3p1_5p3_7p3_15m1_21m1_35m1_105p1_old_210_1_eq_eta :
    cuspForm_105_eta_1m1_3p1_5p3_7p3_15m1_21m1_35m1_105p1_old_210_1 =
      etaQuotientCuspForm 210 sparse![210; 0 => -1, 2 => 1, 4 => 3, 6 => 3, 14 => -1, 20 => -1, 34 => -1, 104 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_105_eta_1m1_3p1_5p3_7p3_15m1_21m1_35m1_105p1_old_210_1_first_coeffs :
    first_coeffs 100 cuspForm_105_eta_1m1_3p1_5p3_7p3_15m1_21m1_35m1_105p1_old_210_1 =
    [0, 0, 0, 1, 1, 2, 2, 4, 2, 4, 0, 4, -2, 1, -6, 3, -7, 0, -11, 2,
     -9, -3, -11, 4, -6, -3, -8, 2, 3, -7, -4, 4, 8, -8, -1, 0, 8, -14, -4, 9,
     14, 3, 4, 13, 19, 0, -2, 14, 8, -3, 3, 4, 12, -12, 1, 4, 4, -2, 12, -10,
     6, -14, 0, 6, -9, -7, 17, -5, -5, -14, 0, -1, -13, 2, 30, -2, 16, -4, 12, 17,
     -5, -14, 7, -11, -6, -12, -19, 7, -27, 7, -11, -5, -2, -8, -39, 18, -6, -3, 3, -15] := by
  eta_coeff

end WeightTwoCusps
