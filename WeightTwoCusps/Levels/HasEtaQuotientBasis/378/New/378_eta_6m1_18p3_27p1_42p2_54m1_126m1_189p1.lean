module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 378

The eta expression is `η(6z)^(-1) η(18z)^3 η(27z) η(42z)^2 η(54z)^(-1) η(126z)^(-1) η(189z)`; see
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

/-- The cuspidal eta quotient `η(6z)^(-1) η(18z)^3 η(27z) η(42z)^2 η(54z)^(-1) η(126z)^(-1) η(189z)` at level 378. -/
abbrev cuspForm_378_eta_6m1_18p3_27p1_42p2_54m1_126m1_189p1 : gamma0CuspForms 378 :=
  etaQuotientCuspForm 378 sparse![378; 5 => -1, 17 => 3, 26 => 1, 41 => 2, 53 => -1, 125 => -1, 188 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_378_eta_6m1_18p3_27p1_42p2_54m1_126m1_189p1_first_coeffs :
    first_coeffs 100 cuspForm_378_eta_6m1_18p3_27p1_42p2_54m1_126m1_189p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 1, 0, 0,
     -1, 0, 0, 2, 0, 0, -2, 0, 0, -2, 0, 0, 0, 0, 0, -1, 0, 0, -2, 0,
     0, -2, 0, 0, -1, 0, 0, 2, 0, 0, -2, 0, 0, -4, 0, 0, 2, 0, 0, 0,
     0, 0, 1, 0, 0, -4, 0, 0, 1, 0, 0, 1, 0, 0, -3, 0, 0, -3, 0, 0] := by
  eta_coeff

end WeightTwoCusps
