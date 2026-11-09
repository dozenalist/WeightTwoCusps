module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 192

The eta expression is `η(z)^(-1) η(3z) η(4z)^4 η(6z) η(8z)^(-1) η(12z)^(-2) η(16z)^(-1) η(24z) η(32z)^2 η(48z) η(64z)^(-1) η(96z)^(-1) η(192z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(3z) η(4z)^4 η(6z) η(8z)^(-1) η(12z)^(-2) η(16z)^(-1) η(24z) η(32z)^2 η(48z) η(64z)^(-1) η(96z)^(-1) η(192z)` at level 192. -/
abbrev cuspForm_192_eta_1m1_3p1_4p4_6p1_8m1_12m2_16m1_24p1_32p2_48p1_64m1_96m1_192p1 : gamma0CuspForms 192 :=
  etaQuotientCuspForm 192 sparse![192; 0 => -1, 2 => 1, 3 => 4, 5 => 1, 7 => -1, 11 => -2, 15 => -1, 23 => 1, 31 => 2, 47 => 1, 63 => -1, 95 => -1, 191 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_192_eta_1m1_3p1_4p4_6p1_8m1_12m2_16m1_24p1_32p2_48p1_64m1_96m1_192p1_first_coeffs :
    first_coeffs 100 cuspForm_192_eta_1m1_3p1_4p4_6p1_8m1_12m2_16m1_24p1_32p2_48p1_64m1_96m1_192p1 =
    [0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 0, 1, -2, 0, -2, -3, 0, -4, 2, -1,
     0, 0, 0, 4, -2, 0, -4, -3, 0, 0, 0, -5, 0, 2, 0, 2, 0, 0, 0, 4,
     -4, -4, 0, 1, 8, 0, 4, -2, 0, 8, 0, 2, 0, 0, 1, 2, 0, -2, 8, 3,
     4, 0, -2, 1, 0, 4, -2, -3, 0, 0, -4, 0, 2, 0, 4, 0, -8, 0, -2, 3,
     0, -4, -8, -5, 0, 0, 0, -5, 8, 0, -4, -2, -16, 0, 4, -2, 0, -16, 0, 1] := by
  eta_coeff

end WeightTwoCusps
