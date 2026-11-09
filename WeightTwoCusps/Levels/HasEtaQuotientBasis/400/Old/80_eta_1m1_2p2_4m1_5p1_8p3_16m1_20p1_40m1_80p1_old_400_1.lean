module

public import WeightTwoCusps.Levels.HasEtaQuotientBasis.«80».New.«80_eta_1m1_2p2_4m1_5p1_8p3_16m1_20p1_40m1_80p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 400

The eta expression is `η(z)^(-1) η(2z)^2 η(4z)^(-1) η(5z) η(8z)^3 η(16z)^(-1) η(20z) η(40z)^(-1) η(80z)`; see
[the local level table](../../TABLE.md#level-400).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_80_eta_1m1_2p2_4m1_5p1_8p3_16m1_20p1_40m1_80p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(4z)^(-1) η(5z) η(8z)^3 η(16z)^(-1) η(20z) η(40z)^(-1) η(80z)` at level 400. -/
abbrev cuspForm_80_eta_1m1_2p2_4m1_5p1_8p3_16m1_20p1_40m1_80p1_old_400_1 : gamma0CuspForms 400 :=
  gamma0RescaleToLevel cuspForm_80_eta_1m1_2p2_4m1_5p1_8p3_16m1_20p1_40m1_80p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_80_eta_1m1_2p2_4m1_5p1_8p3_16m1_20p1_40m1_80p1_old_400_1_eq_eta :
    cuspForm_80_eta_1m1_2p2_4m1_5p1_8p3_16m1_20p1_40m1_80p1_old_400_1 =
      etaQuotientCuspForm 400 sparse![400; 0 => -1, 1 => 2, 3 => -1, 4 => 1, 7 => 3, 15 => -1, 19 => 1, 39 => -1, 79 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_80_eta_1m1_2p2_4m1_5p1_8p3_16m1_20p1_40m1_80p1_old_400_1_first_coeffs :
    first_coeffs 100 cuspForm_80_eta_1m1_2p2_4m1_5p1_8p3_16m1_20p1_40m1_80p1_old_400_1 =
    [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, -2, -2, 0, -3, -1, 0, 0, -2, 0,
     -1, 0, 2, -5, 0, 0, -2, -2, 2, 0, -1, 6, 0, 0, 4, 3, 1, 0, 4, 2,
     0, 0, 2, 9, 0, 0, -1, 1, 0, 0, 0, -6, 2, 0, -2, -2, 0, 0, -4, -4,
     2, 0, -2, -7, 0, 0, 0, -5, -6, 0, -1, 6, 0, 0, 2, 1, -4, 0, 2, -4,
     0, 0, -6, 5, -4, 0, 1, 6, 0, 0, -1, -6, 6, 0, 5, -4, 0, 0, 6, 6] := by
  eta_coeff

end WeightTwoCusps
