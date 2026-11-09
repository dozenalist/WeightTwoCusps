module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 378

The eta expression is `η(z)^2 η(2z)^(-1) η(18z) η(63z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^2 η(2z)^(-1) η(18z) η(63z)^2` at level 378. -/
abbrev cuspForm_378_eta_1p2_2m1_18p1_63p2 : gamma0CuspForms 378 :=
  etaQuotientCuspForm 378 sparse![378; 0 => 2, 1 => -1, 17 => 1, 62 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_378_eta_1p2_2m1_18p1_63p2_first_coeffs :
    first_coeffs 100 cuspForm_378_eta_1p2_2m1_18p1_63p2 =
    [0, 0, 0, 0, 0, 0, 1, -2, 0, 0, 2, 0, 0, 0, 0, -2, 0, 0, 0, 0,
     0, 0, 2, 0, -1, 2, 0, 0, -2, 0, 0, -2, 0, 2, 0, 0, 0, 0, 0, 0,
     -2, 0, 1, 2, 0, 0, -2, 0, 0, 2, 0, 2, 0, 0, 0, -2, 0, 0, -2, 0,
     -2, 0, 0, 0, 0, 0, 0, 2, 0, -2, 6, 0, 0, -2, 0, 0, 0, 0, 2, 0,
     0, 0, 0, 0, 0, -4, 0, 0, -6, 0, 0, 6, 0, 0, 4, 0, -3, -2, 0, 0] := by
  eta_coeff

end WeightTwoCusps
