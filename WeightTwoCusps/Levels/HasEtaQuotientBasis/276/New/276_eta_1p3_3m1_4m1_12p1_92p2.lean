module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 276

The eta expression is `η(z)^3 η(3z)^(-1) η(4z)^(-1) η(12z) η(92z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^3 η(3z)^(-1) η(4z)^(-1) η(12z) η(92z)^2` at level 276. -/
abbrev cuspForm_276_eta_1p3_3m1_4m1_12p1_92p2 : gamma0CuspForms 276 :=
  etaQuotientCuspForm 276 sparse![276; 0 => 3, 2 => -1, 3 => -1, 11 => 1, 91 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_276_eta_1p3_3m1_4m1_12p1_92p2_first_coeffs :
    first_coeffs 100 cuspForm_276_eta_1p3_3m1_4m1_12p1_92p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, -3, 0, 6, -2, -3, 0, 0, -1, 0, 0, 6,
     2, -6, 0, 0, 1, -6, 0, 6, 2, -3, 0, 0, -2, 0, 0, 6, 0, 0, 0, 0,
     -2, -9, 0, 6, -2, 0, 0, 0, 1, 0, 0, 12, 0, -6, 0, 0, 0, -6, 0, 0,
     2, -6, 0, 0, 3, 0, 0, 6, -2, 0, 0, 0, 2, -3, 0, 6, 0, -6, 0, 0,
     0, 0, 0, 6, -2, -6, 0, 0, -2, -6, 0, 12, 0, -3, 0, 0, 0, 0, 0, 6] := by
  eta_coeff

end WeightTwoCusps
