module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 192

The eta expression is `η(z)^(-1) η(3z)^3 η(4z)^(-1) η(8z)^3 η(12z) η(16z)^(-1) η(24z)^(-1) η(48z)`; see
[the local level table](../../TABLE.md#level-192).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^3 η(4z)^(-1) η(8z)^3 η(12z) η(16z)^(-1) η(24z)^(-1) η(48z)` at level 192. -/
abbrev cuspForm_192_eta_1m1_3p3_4m1_8p3_12p1_16m1_24m1_48p1 : gamma0CuspForms 192 :=
  etaQuotientCuspForm 192 sparse![192; 0 => -1, 2 => 3, 3 => -1, 7 => 3, 11 => 1, 15 => -1, 23 => -1, 47 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_192_eta_1m1_3p3_4m1_8p3_12p1_16m1_24m1_48p1_first_coeffs :
    first_coeffs 100 cuspForm_192_eta_1m1_3p3_4m1_8p3_12p1_16m1_24m1_48p1 =
    [0, 0, 1, 1, 2, 0, 3, 2, 4, 0, 2, 2, 2, 0, 0, 0, 0, 0, 1, -2,
     -4, 0, 0, 0, -4, 0, -2, -1, 0, 0, -6, -2, 0, 0, -6, -4, 2, 0, 0, -2,
     -8, 0, -4, 2, -8, 0, 0, -4, 0, 0, -1, -2, -4, 0, -9, -4, 0, 0, 2, -2,
     -4, 0, 0, 2, 0, 0, 4, 2, 4, 0, 0, 8, 4, 0, -2, -1, 8, 0, 18, -2,
     0, 0, 2, 6, 0, 0, 0, 4, 16, 0, 2, 4, 16, 0, 0, 4, 0, 0, 9, 2] := by
  eta_coeff

end WeightTwoCusps
