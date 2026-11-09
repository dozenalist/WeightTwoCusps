module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 198

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^5 η(6z)^(-3) η(9z)^(-2) η(11z) η(18z)^2 η(22z)^(-1) η(33z)^(-1) η(66z)^3 η(99z) η(198z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^5 η(6z)^(-3) η(9z)^(-2) η(11z) η(18z)^2 η(22z)^(-1) η(33z)^(-1) η(66z)^3 η(99z) η(198z)^(-1)` at level 198. -/
abbrev cuspForm_198_eta_1m2_2p2_3p5_6m3_9m2_11p1_18p2_22m1_33m1_66p3_99p1_198m1 : gamma0CuspForms 198 :=
  etaQuotientCuspForm 198 sparse![198; 0 => -2, 1 => 2, 2 => 5, 5 => -3, 8 => -2, 10 => 1, 17 => 2, 21 => -1, 32 => -1, 65 => 3, 98 => 1, 197 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_198_eta_1m2_2p2_3p5_6m3_9m2_11p1_18p2_22m1_33m1_66p3_99p1_198m1_first_coeffs :
    first_coeffs 100 cuspForm_198_eta_1m2_2p2_3p5_6m3_9m2_11p1_18p2_22m1_33m1_66p3_99p1_198m1 =
    [0, 0, 0, 1, 2, 3, 1, -1, -1, 0, 3, 0, 1, -1, 0, 1, -3, 1, -2, 2,
     -2, -5, 0, -1, 3, -4, -4, -1, -1, 4, -1, 2, 2, 0, -1, -5, 2, 2, 0, 1,
     -1, 1, -1, -2, 0, -3, 1, -2, -3, 1, 1, 0, -3, 0, 3, 0, 2, 2, 2, 1,
     -3, -3, -1, 3, 2, -4, 0, 3, 1, -3, -9, -5, -4, 4, 1, 1, -4, 0, -3, -1,
     4, 2, 7, -5, 3, 0, 4, 8, -1, 3, -3, 8, 8, 4, 3, -7, -1, -4, 5, 1] := by
  eta_coeff

end WeightTwoCusps
