module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 243

The eta expression is `η(3z)^(-1) η(9z)^4 η(27z)^(-1) η(81z)^2`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-243).
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

/-- The cuspidal eta quotient `η(3z)^(-1) η(9z)^4 η(27z)^(-1) η(81z)^2` at level 243. -/
abbrev cuspForm_243_eta_3m1_9p4_27m1_81p2 : gamma0CuspForms 243 :=
  etaQuotientCuspForm 243 sparse![243; 2 => -1, 8 => 4, 26 => -1, 80 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_243_eta_3m1_9p4_27m1_81p2_first_coeffs :
    first_coeffs 100 cuspForm_243_eta_3m1_9p4_27m1_81p2 =
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, -1, 0, 0, 1,
     0, 0, -1, 0, 0, 1, 0, 0, -3, 0, 0, -2, 0, 0, 1, 0, 0, 1, 0, 0,
     0, 0, 0, -3, 0, 0, -1, 0, 0, 0, 0, 0, -2, 0, 0, -1, 0, 0, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 2,
     0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -4, 0, 0, -2, 0, 0, 3, 0, 0] := by
  eta_coeff

end WeightTwoCusps
