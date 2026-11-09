module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 38

The eta expression is `η(z)^(-1) η(2z)^3 η(19z)^3 η(38z)^(-1)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-38).
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^3 η(19z)^3 η(38z)^(-1)` at level 38. -/
abbrev cuspForm_38_eta_1m1_2p3_19p3_38m1 : gamma0CuspForms 38 :=
  etaQuotientCuspForm 38 sparse![38; 0 => -1, 1 => 3, 18 => 3, 37 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_38_eta_1m1_2p3_19p3_38m1_first_coeffs :
    first_coeffs 100 cuspForm_38_eta_1m1_2p3_19p3_38m1 =
    [0, 1, 1, -1, 0, -1, -2, 1, -1, -1, 0, 1, 1, -1, 1, 0, 2, 1, 0, 0,
     -4, -1, 4, 0, 2, 6, -4, 3, 2, 1, -2, -6, 3, -4, -1, -7, -2, 0, 0, 4,
     -6, -6, 0, 3, -2, 5, -1, 3, -3, -2, 9, 1, 3, 3, 6, -1, 3, 0, 0, 7,
     6, -1, -6, -3, -2, -2, -4, 1, 4, 1, -8, 2, -2, 1, 0, -9, -1, 3, 5, -4,
     2, -3, -8, 0, -3, -9, 0, 0, -2, 2, 6, -1, 0, 6, 2, 3, -6, 0, -2, 1] := by
  eta_coeff

end WeightTwoCusps
