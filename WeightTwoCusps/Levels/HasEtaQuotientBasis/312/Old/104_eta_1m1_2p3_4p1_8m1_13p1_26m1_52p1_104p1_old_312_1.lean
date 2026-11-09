module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«104».New.«104_eta_1m1_2p3_4p1_8m1_13p1_26m1_52p1_104p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 312

The eta expression is `η(z)^(-1) η(2z)^3 η(4z) η(8z)^(-1) η(13z) η(26z)^(-1) η(52z) η(104z)`; see
[the local level table](../../TABLE.md#level-312).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_104_eta_1m1_2p3_4p1_8m1_13p1_26m1_52p1_104p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^3 η(4z) η(8z)^(-1) η(13z) η(26z)^(-1) η(52z) η(104z)` at level 312. -/
abbrev cuspForm_104_eta_1m1_2p3_4p1_8m1_13p1_26m1_52p1_104p1_old_312_1 : gamma0CuspForms 312 :=
  gamma0RescaleToLevel cuspForm_104_eta_1m1_2p3_4p1_8m1_13p1_26m1_52p1_104p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_104_eta_1m1_2p3_4p1_8m1_13p1_26m1_52p1_104p1_old_312_1_eq_eta :
    cuspForm_104_eta_1m1_2p3_4p1_8m1_13p1_26m1_52p1_104p1_old_312_1 =
      etaQuotientCuspForm 312 sparse![312; 0 => -1, 1 => 3, 3 => 1, 7 => -1, 12 => 1, 25 => -1, 51 => 1, 103 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_104_eta_1m1_2p3_4p1_8m1_13p1_26m1_52p1_104p1_old_312_1_first_coeffs :
    first_coeffs 100 cuspForm_104_eta_1m1_2p3_4p1_8m1_13p1_26m1_52p1_104p1_old_312_1 =
    [0, 0, 0, 0, 0, 0, 1, 1, -1, 0, -2, -3, 2, -1, 0, 2, 0, 2, -1, -1,
     -1, 2, 4, 4, 1, -4, 1, -2, -1, -2, -2, 1, -1, 0, -3, -4, -4, 4, 2, 0,
     2, 0, 0, -2, 4, -2, -2, 5, 2, 6, 3, -2, 1, 0, -1, 2, 0, -4, 2, 1,
     -3, -4, -6, -1, 0, 0, 2, -1, 0, 0, 3, 3, -2, 0, -2, 2, -2, -2, 0, -2,
     -1, 4, 2, -5, 1, 6, -1, -4, -2, -4, 6, -1, 2, 0, 0, 2, 1, 0, -1, 5] := by
  eta_coeff

end WeightTwoCusps
