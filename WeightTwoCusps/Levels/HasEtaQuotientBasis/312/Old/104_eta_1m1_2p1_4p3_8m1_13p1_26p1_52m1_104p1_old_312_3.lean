module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«104».New.«104_eta_1m1_2p1_4p3_8m1_13p1_26p1_52m1_104p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 312

The eta expression is `η(3z)^(-1) η(6z) η(12z)^3 η(24z)^(-1) η(39z) η(78z) η(156z)^(-1) η(312z)`; see
[the local level table](../../TABLE.md#level-312).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(3z)` of `cuspForm_104_eta_1m1_2p1_4p3_8m1_13p1_26p1_52m1_104p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-1) η(6z) η(12z)^3 η(24z)^(-1) η(39z) η(78z) η(156z)^(-1) η(312z)` at level 312. -/
abbrev cuspForm_104_eta_1m1_2p1_4p3_8m1_13p1_26p1_52m1_104p1_old_312_3 : gamma0CuspForms 312 :=
  gamma0Rescale cuspForm_104_eta_1m1_2p1_4p3_8m1_13p1_26p1_52m1_104p1 3

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_104_eta_1m1_2p1_4p3_8m1_13p1_26p1_52m1_104p1_old_312_3_eq_eta :
    cuspForm_104_eta_1m1_2p1_4p3_8m1_13p1_26p1_52m1_104p1_old_312_3 =
      etaQuotientCuspForm 312 sparse![312; 2 => -1, 5 => 1, 11 => 3, 23 => -1, 38 => 1, 77 => 1, 155 => -1, 311 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_104_eta_1m1_2p1_4p3_8m1_13p1_26p1_52m1_104p1_old_312_3_first_coeffs :
    first_coeffs 100 cuspForm_104_eta_1m1_2p1_4p3_8m1_13p1_26p1_52m1_104p1_old_312_3 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0,
     0, 2, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 1, 0, 0, 0,
     0, 0, -1, 0, 0, -1, 0, 0, 1, 0, 0, -2, 0, 0, -3, 0, 0, -1, 0, 0,
     -3, 0, 0, 1, 0, 0, 0, 0, 0, -2, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0,
     0, 2, 0, 0, -1, 0, 0, -4, 0, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0, -4] := by
  eta_coeff

end WeightTwoCusps
