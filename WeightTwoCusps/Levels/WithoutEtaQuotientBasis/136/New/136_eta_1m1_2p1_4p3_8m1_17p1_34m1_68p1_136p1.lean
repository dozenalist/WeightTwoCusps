module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 136

The eta expression is `η(z)^(-1) η(2z) η(4z)^3 η(8z)^(-1) η(17z) η(34z)^(-1) η(68z) η(136z)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-136).
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(4z)^3 η(8z)^(-1) η(17z) η(34z)^(-1) η(68z) η(136z)` at level 136. -/
abbrev cuspForm_136_eta_1m1_2p1_4p3_8m1_17p1_34m1_68p1_136p1 : gamma0CuspForms 136 :=
  etaQuotientCuspForm 136 sparse![136; 0 => -1, 1 => 1, 3 => 3, 7 => -1, 16 => 1, 33 => -1, 67 => 1, 135 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_136_eta_1m1_2p1_4p3_8m1_17p1_34m1_68p1_136p1_first_coeffs :
    first_coeffs 100 cuspForm_136_eta_1m1_2p1_4p3_8m1_17p1_34m1_68p1_136p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, -1, 0, 1, -1, 1, 0, -1, -1,
     1, -1, -2, 0, -1, -1, -1, -2, -4, 2, 0, 0, -1, -4, 0, 0, 2, -2, 2, 2,
     -1, 2, -1, -1, 3, 2, -1, -1, -1, 2, 2, 0, 2, 1, 0, 1, 0, 0, -1, 1,
     0, -2, -1, 2, 1, 0, 3, -1, -1, 0, 0, 0, -1, 2, 3, 2, 0, -2, 0, 2,
     -1, 2, -2, 1, 4, 1, 2, -3, 3, -2, -1, -2, -2, 2, 2, -2, -1, 0, -3, 2] := by
  eta_coeff

end WeightTwoCusps
