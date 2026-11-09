module

public import WeightTwoCusps.Levels.WithoutEtaQuotientBasis.«198».New.«198_eta_1m1_2p2_6p1_9p1_18m1_66p1_198p1»
public import WeightTwoCusps.Oldforms
public import WeightTwoCusps.Tactic.EtaOldform

/-!
# A cuspidal eta basis vector at level 396

The eta expression is `η(z)^(-1) η(2z)^2 η(6z) η(9z) η(18z)^(-1) η(66z) η(198z)`; see
[the local level table](../../TABLE.md#level-396).
This is a vector of the complete cuspidal eta basis.

This is the oldform `f(1z)` of `cuspForm_198_eta_1m1_2p2_6p1_9p1_18m1_66p1_198p1`,
with the original source and total dilation recorded in its name.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(6z) η(9z) η(18z)^(-1) η(66z) η(198z)` at level 396. -/
abbrev cuspForm_198_eta_1m1_2p2_6p1_9p1_18m1_66p1_198p1_old_396_1 : gamma0CuspForms 396 :=
  gamma0RescaleToLevel cuspForm_198_eta_1m1_2p2_6p1_9p1_18m1_66p1_198p1 1 (by decide)

/-- The degeneracy lift is the corresponding cuspidal eta quotient. -/
theorem cuspForm_198_eta_1m1_2p2_6p1_9p1_18m1_66p1_198p1_old_396_1_eq_eta :
    cuspForm_198_eta_1m1_2p2_6p1_9p1_18m1_66p1_198p1_old_396_1 =
      etaQuotientCuspForm 396 sparse![396; 0 => -1, 1 => 2, 5 => 1, 8 => 1, 17 => -1, 65 => 1, 197 => 1] := by
  eta_oldform

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_198_eta_1m1_2p2_6p1_9p1_18m1_66p1_198p1_old_396_1_first_coeffs :
    first_coeffs 100 cuspForm_198_eta_1m1_2p2_6p1_9p1_18m1_66p1_198p1_old_396_1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, -1, 0,
     -2, 0, 0, -3, -1, 0, 0, 0, 0, 0, -1, 0, 2, 0, 0, 0, 1, 0, -2, 0,
     0, 0, 2, 0, 0, 0, 0, 6, -1, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, -3,
     0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, -1, 0, -4, 0, 0, -1, -2, 0,
     -1, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0, -2, 0, 0, -6, 1, 0, -2, 0] := by
  eta_coeff

end WeightTwoCusps
