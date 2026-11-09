module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 378

The eta expression is `η(6z)^2 η(18z)^(-1) η(27z) η(42z)^(-1) η(126z)^3 η(189z) η(378z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(6z)^2 η(18z)^(-1) η(27z) η(42z)^(-1) η(126z)^3 η(189z) η(378z)^(-1)` at level 378. -/
abbrev cuspForm_378_eta_6p2_18m1_27p1_42m1_126p3_189p1_378m1 : gamma0CuspForms 378 :=
  etaQuotientCuspForm 378 sparse![378; 5 => 2, 17 => -1, 26 => 1, 41 => -1, 125 => 3, 188 => 1, 377 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_378_eta_6p2_18m1_27p1_42m1_126p3_189p1_378m1_first_coeffs :
    first_coeffs 100 cuspForm_378_eta_6p2_18m1_27p1_42m1_126p3_189p1_378m1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, -1,
     0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 1, 0, 0,
     2, 0, 0, 2, 0, 0, 1, 0, 0, -2, 0, 0, -3, 0, 0, -4, 0, 0, 1, 0,
     0, 1, 0, 0, -1, 0, 0, 2, 0, 0, -2, 0, 0, -1, 0, 0, 2, 0, 0, 3,
     0, 0, 4, 0, 0, -1, 0, 0, -2, 0, 0, -2, 0, 0, 0, 0, 0, -3, 0, 0] := by
  eta_coeff

end WeightTwoCusps
