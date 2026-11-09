module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 198

The eta expression is `η(z)^(-1) η(2z)^3 η(3z) η(6z)^(-1) η(22z) η(33z) η(66z)^(-1) η(99z)^(-1) η(198z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^3 η(3z) η(6z)^(-1) η(22z) η(33z) η(66z)^(-1) η(99z)^(-1) η(198z)^2` at level 198. -/
abbrev cuspForm_198_eta_1m1_2p3_3p1_6m1_22p1_33p1_66m1_99m1_198p2 : gamma0CuspForms 198 :=
  etaQuotientCuspForm 198 sparse![198; 0 => -1, 1 => 3, 2 => 1, 5 => -1, 21 => 1, 32 => 1, 65 => -1, 98 => -1, 197 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_198_eta_1m1_2p3_3p1_6m1_22p1_33p1_66m1_99m1_198p2_first_coeffs :
    first_coeffs 100 cuspForm_198_eta_1m1_2p3_3p1_6m1_22p1_33p1_66m1_99m1_198p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, -1, -1, -2, -1, 1, 0,
     1, -2, 1, 3, 0, 2, 0, 1, -1, 0, 0, -2, 1, 0, -1, -3, 0, 1, 1, 0,
     0, -1, -3, 1, -1, -2, 0, 0, 3, 1, 0, 2, -1, 1, 1, -1, -3, 2, 3, 1,
     1, 3, 0, 0, 4, 0, -1, -5, 1, -3, -3, -1, 0, -5, 2, 6, -3, 1, -1, 0,
     -1, -1, 2, 1, -6, 2, -1, 4, 0, 0, -3, -5, -2, -6, 3, 1, 2, -1, 1, 1] := by
  eta_coeff

end WeightTwoCusps
