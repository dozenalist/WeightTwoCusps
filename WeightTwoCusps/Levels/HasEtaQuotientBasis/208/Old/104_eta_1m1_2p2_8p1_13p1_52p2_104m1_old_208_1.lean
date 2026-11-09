module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«104».New.«104_eta_1m1_2p2_8p1_13p1_52p2_104m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 208

The eta expression is `η(z)^(-1) η(2z)^2 η(8z) η(13z) η(52z)^2 η(104z)^(-1)`; see
[the local level table](../../TABLE.md#level-208).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_104_eta_1m1_2p2_8p1_13p1_52p2_104m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(8z) η(13z) η(52z)^2 η(104z)^(-1)` at level 208. -/
abbrev cuspForm_104_eta_1m1_2p2_8p1_13p1_52p2_104m1_old_208_1 : gamma0CuspForms 208 :=
  gamma0RescaleToLevel cuspForm_104_eta_1m1_2p2_8p1_13p1_52p2_104m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_104_eta_1m1_2p2_8p1_13p1_52p2_104m1_old_208_1_eq_eta :
    cuspForm_104_eta_1m1_2p2_8p1_13p1_52p2_104m1_old_208_1 =
      etaQuotientCuspForm 208 sparse![208; 0 => -1, 1 => 2, 7 => 1, 12 => 1, 51 => 2, 103 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_104_eta_1m1_2p2_8p1_13p1_52p2_104m1_old_208_1_first_coeffs :
    first_coeffs 100 cuspForm_104_eta_1m1_2p2_8p1_13p1_52p2_104m1_old_208_1 =
    [0, 1, 1, 0, 1, 0, 0, 1, 0, -1, -1, 1, -1, 0, -1, -2, 1, -2, -1, -1,
     -2, 0, 2, 0, -2, 1, 0, -2, 0, 0, -1, 1, 0, 0, 0, 0, 2, 0, 0, 0,
     1, 2, -1, 2, 2, 0, 2, 1, -1, 1, 1, 2, 0, -2, -4, -2, 1, 0, 4, -3,
     0, 2, 2, -1, 1, 0, 4, 7, -3, 4, 0, 3, 4, -2, -5, -2, 4, -2, 1, 6,
     -2, 1, -2, -5, -2, 0, 0, 0, -4, -2, 0, -1, -2, -4, 3, -6, -2, -2, -5, -3] := by
  eta_coeff

end WeightTwoCusps
