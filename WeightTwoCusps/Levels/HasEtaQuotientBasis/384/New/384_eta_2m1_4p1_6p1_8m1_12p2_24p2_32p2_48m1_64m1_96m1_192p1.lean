module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 384

The eta expression is `η(2z)^(-1) η(4z) η(6z) η(8z)^(-1) η(12z)^2 η(24z)^2 η(32z)^2 η(48z)^(-1) η(64z)^(-1) η(96z)^(-1) η(192z)`; see
[the local level table](../../TABLE.md#level-384).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-1) η(4z) η(6z) η(8z)^(-1) η(12z)^2 η(24z)^2 η(32z)^2 η(48z)^(-1) η(64z)^(-1) η(96z)^(-1) η(192z)` at level 384. -/
abbrev cuspForm_384_eta_2m1_4p1_6p1_8m1_12p2_24p2_32p2_48m1_64m1_96m1_192p1 : gamma0CuspForms 384 :=
  etaQuotientCuspForm 384 sparse![384; 1 => -1, 3 => 1, 5 => 1, 7 => -1, 11 => 2, 23 => 2, 31 => 2, 47 => -1, 63 => -1, 95 => -1, 191 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_384_eta_2m1_4p1_6p1_8m1_12p2_24p2_32p2_48m1_64m1_96m1_192p1_first_coeffs :
    first_coeffs 100 cuspForm_384_eta_2m1_4p1_6p1_8m1_12p2_24p2_32p2_48m1_64m1_96m1_192p1 =
    [0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 3, 0, 0, 0, 1,
     0, 3, 0, 4, 0, 2, 0, 1, 0, 3, 0, 3, 0, -1, 0, 0, 0, 0, 0, -2,
     0, 2, 0, -1, 0, -1, 0, -6, 0, -2, 0, 0, 0, -5, 0, -6, 0, -1, 0, -3,
     0, -4, 0, -3, 0, -2, 0, -1, 0, -4, 0, 4, 0, -4, 0, -2, 0, -8, 0, -1,
     0, 0, 0, -1, 0, -2, 0, -7, 0, -2, 0, 2, 0, -7, 0, -10, 0, 2, 0, -1] := by
  eta_coeff

end WeightTwoCusps
