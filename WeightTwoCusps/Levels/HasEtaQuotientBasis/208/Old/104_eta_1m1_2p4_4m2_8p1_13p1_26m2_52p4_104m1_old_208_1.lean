module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«104».New.«104_eta_1m1_2p4_4m2_8p1_13p1_26m2_52p4_104m1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 208

The eta expression is `η(z)^(-1) η(2z)^4 η(4z)^(-2) η(8z) η(13z) η(26z)^(-2) η(52z)^4 η(104z)^(-1)`; see
[the local level table](../../TABLE.md#level-208).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_104_eta_1m1_2p4_4m2_8p1_13p1_26m2_52p4_104m1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^4 η(4z)^(-2) η(8z) η(13z) η(26z)^(-2) η(52z)^4 η(104z)^(-1)` at level 208. -/
abbrev cuspForm_104_eta_1m1_2p4_4m2_8p1_13p1_26m2_52p4_104m1_old_208_1 : gamma0CuspForms 208 :=
  gamma0RescaleToLevel cuspForm_104_eta_1m1_2p4_4m2_8p1_13p1_26m2_52p4_104m1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_104_eta_1m1_2p4_4m2_8p1_13p1_26m2_52p4_104m1_old_208_1_eq_eta :
    cuspForm_104_eta_1m1_2p4_4m2_8p1_13p1_26m2_52p4_104m1_old_208_1 =
      etaQuotientCuspForm 208 sparse![208; 0 => -1, 1 => 4, 3 => -2, 7 => 1, 12 => 1, 25 => -2, 51 => 4, 103 => -1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_104_eta_1m1_2p4_4m2_8p1_13p1_26m2_52p4_104m1_old_208_1_first_coeffs :
    first_coeffs 100 cuspForm_104_eta_1m1_2p4_4m2_8p1_13p1_26m2_52p4_104m1_old_208_1 =
    [0, 0, 0, 1, 1, -2, -1, 1, -1, -1, -1, 1, 1, 0, 1, 0, 1, -1, 3, 1,
     -3, 2, 0, 2, -1, -1, 0, -3, -1, 0, 1, -5, -1, 2, -3, -1, -2, 2, 4, 0,
     3, 2, -1, -3, 6, 4, -4, 5, 1, 5, -1, -5, 1, -4, -3, -6, 1, 0, 0, 3,
     -3, 2, -2, -3, 1, -1, 2, 3, -3, -2, 1, -1, 2, 2, 3, 2, 2, -6, 1, 4,
     -3, 0, 2, 3, -1, 6, -3, 0, -6, -6, 0, -2, 0, 0, 5, 4, -1, -8, -1, -1] := by
  eta_coeff

end WeightTwoCusps
