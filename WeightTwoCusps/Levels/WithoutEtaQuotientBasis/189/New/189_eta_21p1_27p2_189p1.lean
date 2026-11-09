module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A supporting cuspidal eta quotient at level 189

The eta expression is `η(21z) η(27z)^2 η(189z)`; see
[the local level table](../../../HasEtaQuotientBasis/TABLE.md#level-189).
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

/-- The cuspidal eta quotient `η(21z) η(27z)^2 η(189z)` at level 189. -/
abbrev cuspForm_189_eta_21p1_27p2_189p1 : gamma0CuspForms 189 :=
  etaQuotientCuspForm 189 sparse![189; 20 => 1, 26 => 2, 188 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_189_eta_21p1_27p2_189p1_first_coeffs :
    first_coeffs 100 cuspForm_189_eta_21p1_27p2_189p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -2, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 2,
     0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
