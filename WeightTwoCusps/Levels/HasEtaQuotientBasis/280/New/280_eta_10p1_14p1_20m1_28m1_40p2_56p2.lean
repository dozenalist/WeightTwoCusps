module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 280

The eta expression is `η(10z) η(14z) η(20z)^(-1) η(28z)^(-1) η(40z)^2 η(56z)^2`; see
[the local level table](../../TABLE.md#level-280).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(10z) η(14z) η(20z)^(-1) η(28z)^(-1) η(40z)^2 η(56z)^2` at level 280. -/
abbrev cuspForm_280_eta_10p1_14p1_20m1_28m1_40p2_56p2 : gamma0CuspForms 280 :=
  etaQuotientCuspForm 280 sparse![280; 9 => 1, 13 => 1, 19 => -1, 27 => -1, 39 => 2, 55 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_280_eta_10p1_14p1_20m1_28m1_40p2_56p2_first_coeffs :
    first_coeffs 100 cuspForm_280_eta_10p1_14p1_20m1_28m1_40p2_56p2 =
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0,
     0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0,
     0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1,
     0, 1, 0, -1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 1, 0, 0, 0, 2, 0, 1,
     0, -1, 0, 0, 0, 0, 0, -2, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, -1] := by
  eta_coeff

end WeightTwoCusps
