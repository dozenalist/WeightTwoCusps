module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 196

The eta expression is `η(z)^(-1) η(2z)^2 η(7z)^(-1) η(14z)^4 η(28z)^(-1) η(98z)^2 η(196z)^(-1)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-196).
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(7z)^(-1) η(14z)^4 η(28z)^(-1) η(98z)^2 η(196z)^(-1)` at level 196. -/
abbrev cuspForm_196_eta_1m1_2p2_7m1_14p4_28m1_98p2_196m1 : gamma0CuspForms 196 :=
  etaQuotientCuspForm 196 sparse![196; 0 => -1, 1 => 2, 6 => -1, 13 => 4, 27 => -1, 97 => 2, 195 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_196_eta_1m1_2p2_7m1_14p4_28m1_98p2_196m1_first_coeffs :
    first_coeffs 100 cuspForm_196_eta_1m1_2p2_7m1_14p4_28m1_98p2_196m1 =
    [0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 2, 0, 0, 1, -2, -1, 0, -1, 0,
     0, -2, 0, 0, 0, -3, 0, 0, -1, 2, -2, 0, -1, 0, 0, 0, -3, -2, 0, -2,
     0, 0, -2, -2, 2, 0, 0, 0, 0, 1, -1, -4, 0, 2, 0, 0, 1, -2, 0, 0,
     -2, 0, 0, 1, 1, 2, 0, 2, 0, 0, 0, 2, -1, 0, 4, 0, 0, 0, 2, 6,
     0, -1, 0, 0, 2, 0, 0, 0, 0, 0, 0, -4, 4, 0, 0, -2, 0, 0, 1, 4] := by
  eta_coeff

end WeightTwoCusps
