module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 378

The eta expression is `η(3z) η(18z) η(21z) η(126z)`; see
[the local level table](../../TABLE.md#level-378).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z) η(18z) η(21z) η(126z)` at level 378. -/
abbrev cuspForm_378_eta_3p1_18p1_21p1_126p1 : gamma0CuspForms 378 :=
  etaQuotientCuspForm 378 sparse![378; 2 => 1, 17 => 1, 20 => 1, 125 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_378_eta_3p1_18p1_21p1_126p1_first_coeffs :
    first_coeffs 100 cuspForm_378_eta_3p1_18p1_21p1_126p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0,
     0, 0, 1, 0, 0, -1, 0, 0, 1, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0,
     -1, 0, 0, -3, 0, 0, 1, 0, 0, -2, 0, 0, -1, 0, 0, 1, 0, 0, -1, 0,
     0, 2, 0, 0, 0, 0, 0, 1, 0, 0, -2, 0, 0, 1, 0, 0, 0, 0, 0, 2,
     0, 0, 0, 0, 0, 4, 0, 0, 1, 0, 0, -3, 0, 0, 0, 0, 0, 1, 0, 0] := by
  eta_coeff

end WeightTwoCusps
