module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 198

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^3 η(6z)^(-2) η(9z)^(-1) η(11z)^(-1) η(18z) η(22z) η(33z)^2 η(66z)^(-1) η(99z)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-198).
The table has full eta basis = NO at this level: these supporting forms
do not span the whole cusp-form space.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^3 η(6z)^(-2) η(9z)^(-1) η(11z)^(-1) η(18z) η(22z) η(33z)^2 η(66z)^(-1) η(99z)` at level 198. -/
abbrev cuspForm_198_eta_1m2_2p3_3p3_6m2_9m1_11m1_18p1_22p1_33p2_66m1_99p1 : gamma0CuspForms 198 :=
  etaQuotientCuspForm 198 sparse![198; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 8 => -1, 10 => -1, 17 => 1, 21 => 1, 32 => 2, 65 => -1, 98 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_198_eta_1m2_2p3_3p3_6m2_9m1_11m1_18p1_22p1_33p2_66m1_99p1_first_coeffs :
    first_coeffs 100 cuspForm_198_eta_1m2_2p3_3p3_6m2_9m1_11m1_18p1_22p1_33p2_66m1_99p1 =
    [0, 0, 0, 0, 0, 1, 2, 2, 1, -1, 0, 0, 1, 1, -2, 0, 0, 4, 2, -1,
     0, -2, 0, -2, 0, -3, -1, 1, 2, 1, -2, 1, -2, 0, -1, 0, -6, -2, -1, 0,
     0, -3, 3, -3, 0, -2, -1, -5, -3, -3, -2, 2, 1, 2, -2, 1, 2, 2, -5, -1,
     -3, 3, 8, 2, 0, -1, 1, 2, 4, -2, 1, -6, 4, 6, -3, 3, -1, 1, -3, 2,
     0, 1, 2, 4, 4, -2, 3, 2, 0, 2, 4, -5, 1, -3, 7, 1, -2, 6, -2, 0] := by
  eta_coeff

end WeightTwoCusps
