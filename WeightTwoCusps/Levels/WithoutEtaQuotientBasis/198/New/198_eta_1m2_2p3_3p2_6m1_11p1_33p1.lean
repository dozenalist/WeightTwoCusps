module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 198

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^2 η(6z)^(-1) η(11z) η(33z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^2 η(6z)^(-1) η(11z) η(33z)` at level 198. -/
abbrev cuspForm_198_eta_1m2_2p3_3p2_6m1_11p1_33p1 : gamma0CuspForms 198 :=
  etaQuotientCuspForm 198 sparse![198; 0 => -2, 1 => 3, 2 => 2, 5 => -1, 10 => 1, 32 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_198_eta_1m2_2p3_3p2_6m1_11p1_33p1_first_coeffs :
    first_coeffs 100 cuspForm_198_eta_1m2_2p3_3p2_6m1_11p1_33p1 =
    [0, 0, 1, 2, 2, 2, 1, 2, 2, 2, 3, 0, 2, 1, 0, 0, -2, 3, 0, 0,
     0, -3, 1, 0, 1, -2, -4, 0, -3, -2, -1, -2, -1, -1, -2, -5, -6, -2, 0, -5,
     -4, -7, -4, -1, -1, -2, -7, 0, 0, -2, -6, -4, 1, -2, -1, -1, -4, 0, 4, 6,
     -2, 1, 5, 1, 2, 0, 1, -2, 5, 4, -4, -8, 8, 3, 1, 0, -9, 2, 0, 8,
     2, -2, 12, 3, 1, 2, 2, 14, -1, 8, -1, -6, 4, 4, 11, 3, -1, 6, 4, 2] := by
  eta_coeff

end WeightTwoCusps
