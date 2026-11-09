module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 276

The eta expression is `η(z)^(-1) η(3z)^3 η(4z) η(12z)^(-1) η(276z)^2`; see
[the local level table](../../TABLE.md#level-276).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^3 η(4z) η(12z)^(-1) η(276z)^2` at level 276. -/
abbrev cuspForm_276_eta_1m1_3p3_4p1_12m1_276p2 : gamma0CuspForms 276 :=
  etaQuotientCuspForm 276 sparse![276; 0 => -1, 2 => 3, 3 => 1, 11 => -1, 275 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_276_eta_1m1_3p3_4p1_12m1_276p2_first_coeffs :
    first_coeffs 100 cuspForm_276_eta_1m1_3p3_4p1_12m1_276p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 1, 1, 2, 0, 1, 0, 0, 0, -2, 0, -2, 0, 0, -2, 0, 0, 1,
     0, -4, 0, -4, 0, 0, 0, 0, -1, 4, 0, 0, 0, 0, 0, -2, 0, -2, 0, 4,
     2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 1, 6, 0, 2, 0, 0, 0, 0,
     0, -2, 0, 0, 2, 0, 0, 1, 0, 0, 0, -4, 0, 0, 0, 4, -2, 4, 0, 0] := by
  eta_coeff

end WeightTwoCusps
