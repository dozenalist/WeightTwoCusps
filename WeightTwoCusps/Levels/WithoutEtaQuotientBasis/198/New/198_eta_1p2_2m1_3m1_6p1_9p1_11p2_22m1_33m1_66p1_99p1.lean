module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 198

The eta expression is `η(z)^2 η(2z)^(-1) η(3z)^(-1) η(6z) η(9z) η(11z)^2 η(22z)^(-1) η(33z)^(-1) η(66z) η(99z)`; see
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

/-- The cuspidal eta quotient `η(z)^2 η(2z)^(-1) η(3z)^(-1) η(6z) η(9z) η(11z)^2 η(22z)^(-1) η(33z)^(-1) η(66z) η(99z)` at level 198. -/
abbrev cuspForm_198_eta_1p2_2m1_3m1_6p1_9p1_11p2_22m1_33m1_66p1_99p1 : gamma0CuspForms 198 :=
  etaQuotientCuspForm 198 sparse![198; 0 => 2, 1 => -1, 2 => -1, 5 => 1, 8 => 1, 10 => 2, 21 => -1, 32 => -1, 65 => 1, 98 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_198_eta_1p2_2m1_3m1_6p1_9p1_11p2_22m1_33m1_66p1_99p1_first_coeffs :
    first_coeffs 100 cuspForm_198_eta_1p2_2m1_3m1_6p1_9p1_11p2_22m1_33m1_66p1_99p1 =
    [0, 0, 0, 0, 0, 0, 1, -2, 0, 1, 0, 0, 1, 0, 0, -1, 0, -2, 3, 0,
     -2, 0, 0, -2, -1, 4, 2, 0, 0, 2, -2, 0, 0, 0, 0, 2, -9, 0, 0, 0,
     -2, 4, 2, 2, 0, 0, 0, 2, -1, 0, 2, 0, 0, -2, -3, 0, 2, 0, 4, 0,
     -2, -4, -2, -2, 0, -2, 1, 0, -2, -1, 0, 4, 11, -2, 0, 3, 2, -2, 0, -2,
     0, -2, 0, -6, 2, 0, -2, 2, 0, 0, 4, 4, 2, -3, -4, -4, -1, -4, -2, 1] := by
  eta_coeff

end WeightTwoCusps
