module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 198

The eta expression is `η(z)^(-1) η(2z)^2 η(6z) η(9z) η(18z)^(-1) η(66z) η(198z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(6z) η(9z) η(18z)^(-1) η(66z) η(198z)` at level 198. -/
abbrev cuspForm_198_eta_1m1_2p2_6p1_9p1_18m1_66p1_198p1 : gamma0CuspForms 198 :=
  etaQuotientCuspForm 198 sparse![198; 0 => -1, 1 => 2, 5 => 1, 8 => 1, 17 => -1, 65 => 1, 197 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_198_eta_1m1_2p2_6p1_9p1_18m1_66p1_198p1_first_coeffs :
    first_coeffs 100 cuspForm_198_eta_1m1_2p2_6p1_9p1_18m1_66p1_198p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, -1, 0,
     -2, 0, 0, -3, -1, 0, 0, 0, 0, 0, -1, 0, 2, 0, 0, 0, 1, 0, -2, 0,
     0, 0, 2, 0, 0, 0, 0, 6, -1, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, -3,
     0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, -1, 0, -4, 0, 0, -1, -2, 0,
     -1, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0, -2, 0, 0, -6, 1, 0, -2, 0] := by
  eta_coeff

end WeightTwoCusps
