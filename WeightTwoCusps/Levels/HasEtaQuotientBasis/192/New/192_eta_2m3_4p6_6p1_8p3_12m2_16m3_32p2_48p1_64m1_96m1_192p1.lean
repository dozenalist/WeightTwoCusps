module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 192

The eta expression is `η(2z)^(-3) η(4z)^6 η(6z) η(8z)^3 η(12z)^(-2) η(16z)^(-3) η(32z)^2 η(48z) η(64z)^(-1) η(96z)^(-1) η(192z)`; see
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

/-- The cuspidal eta quotient `η(2z)^(-3) η(4z)^6 η(6z) η(8z)^3 η(12z)^(-2) η(16z)^(-3) η(32z)^2 η(48z) η(64z)^(-1) η(96z)^(-1) η(192z)` at level 192. -/
abbrev cuspForm_192_eta_2m3_4p6_6p1_8p3_12m2_16m3_32p2_48p1_64m1_96m1_192p1 : gamma0CuspForms 192 :=
  etaQuotientCuspForm 192 sparse![192; 1 => -3, 3 => 6, 5 => 1, 7 => 3, 11 => -2, 15 => -3, 31 => 2, 47 => 1, 63 => -1, 95 => -1, 191 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_192_eta_2m3_4p6_6p1_8p3_12m2_16m3_32p2_48p1_64m1_96m1_192p1_first_coeffs :
    first_coeffs 100 cuspForm_192_eta_2m3_4p6_6p1_8p3_12m2_16m3_32p2_48p1_64m1_96m1_192p1 =
    [0, 0, 0, 0, 0, 1, 0, 3, 0, 3, 0, 3, 0, 0, 0, -9, 0, -6, 0, -3,
     0, -3, 0, 12, 0, 0, 0, -9, 0, -1, 0, -15, 0, 3, 0, 6, 0, -2, 0, 12,
     0, -6, 0, 3, 0, 3, 0, -6, 0, 12, 0, 6, 0, 11, 0, 6, 0, -3, 0, 9,
     0, 2, 0, 3, 0, 6, 0, -9, 0, 0, 0, 0, 0, 0, 0, 0, 0, -12, 0, 9,
     0, -6, 0, -15, 0, -10, 0, -15, 0, 0, 0, -6, 0, 3, 0, -6, 0, -24, 0, 3] := by
  eta_coeff

end WeightTwoCusps
