module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 198

The eta expression is `η(z)^(-2) η(2z) η(3z)^6 η(6z)^(-2) η(9z)^(-2) η(11z)^2 η(18z) η(22z)^(-1) η(33z)^(-2) η(66z)^2 η(99z)^2 η(198z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^6 η(6z)^(-2) η(9z)^(-2) η(11z)^2 η(18z) η(22z)^(-1) η(33z)^(-2) η(66z)^2 η(99z)^2 η(198z)^(-1)` at level 198. -/
abbrev cuspForm_198_eta_1m2_2p1_3p6_6m2_9m2_11p2_18p1_22m1_33m2_66p2_99p2_198m1 : gamma0CuspForms 198 :=
  etaQuotientCuspForm 198 sparse![198; 0 => -2, 1 => 1, 2 => 6, 5 => -2, 8 => -2, 10 => 2, 17 => 1, 21 => -1, 32 => -2, 65 => 2, 98 => 2, 197 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_198_eta_1m2_2p1_3p6_6m2_9m2_11p2_18p1_22m1_33m2_66p2_99p2_198m1_first_coeffs :
    first_coeffs 100 cuspForm_198_eta_1m2_2p1_3p6_6m2_9m2_11p2_18p1_22m1_33m2_66p2_99p2_198m1 =
    [0, 0, 0, 1, 2, 4, 2, 2, 0, 3, 2, 0, 2, 2, 6, -3, -6, -4, -2, 4,
     -6, -2, 0, 0, 0, -14, -2, -2, 2, -4, -6, 2, 4, 1, -4, -8, -2, 6, 4, 4,
     6, 4, 4, -12, -2, -1, 6, 14, -4, 0, -12, -2, -6, -10, 4, 0, -2, 0, -8, 6,
     -6, 6, -8, -6, 6, 4, 2, 2, 0, -5, -12, 4, 8, 12, 8, 8, -8, -2, 0, -2,
     14, -3, 8, -16, 4, 0, -8, 8, 0, 2, -2, 0, 14, -5, 14, -12, 0, -2, 8, 3] := by
  eta_coeff

end WeightTwoCusps
