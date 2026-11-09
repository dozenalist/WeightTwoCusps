module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 192

The eta expression is `η(z)^(-1) η(3z)^3 η(8z) η(16z)^(-1) η(32z)^2 η(48z) η(64z)^(-1) η(96z)^(-1) η(192z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z)^3 η(8z) η(16z)^(-1) η(32z)^2 η(48z) η(64z)^(-1) η(96z)^(-1) η(192z)` at level 192. -/
abbrev cuspForm_192_eta_1m1_3p3_8p1_16m1_32p2_48p1_64m1_96m1_192p1 : gamma0CuspForms 192 :=
  etaQuotientCuspForm 192 sparse![192; 0 => -1, 2 => 3, 7 => 1, 15 => -1, 31 => 2, 47 => 1, 63 => -1, 95 => -1, 191 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_192_eta_1m1_3p3_8p1_16m1_32p2_48p1_64m1_96m1_192p1_first_coeffs :
    first_coeffs 100 cuspForm_192_eta_1m1_3p3_8p1_16m1_32p2_48p1_64m1_96m1_192p1 =
    [0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 2, 1, 2, 0, 0, 1, 0, 0, 0, -1,
     0, 0, 2, 0, -2, 0, 0, 1, 0, 0, -2, -1, 0, 0, -4, -2, 0, 0, -2, -4,
     -4, 0, -2, 1, -8, 0, -4, -2, 0, 0, 0, -2, 0, 0, -5, -2, 0, 0, -2, -1,
     -4, 0, 4, 1, 0, 0, 4, 1, 0, 0, 0, 4, 2, 0, -4, 0, 8, 0, 10, -1,
     0, 0, 4, 3, 0, 0, 2, 7, 8, 0, 2, 2, 16, 0, 0, 2, 0, 0, 8, 1] := by
  eta_coeff

end WeightTwoCusps
