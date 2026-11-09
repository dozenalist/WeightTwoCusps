module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 384

The eta expression is `η(2z)^(-1) η(4z)^2 η(6z) η(12z)^(-1) η(16z)^(-1) η(24z)^(-1) η(32z) η(48z)^2 η(64z)^(-1) η(96z)^2 η(192z)`; see
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

/-- The cuspidal eta quotient `η(2z)^(-1) η(4z)^2 η(6z) η(12z)^(-1) η(16z)^(-1) η(24z)^(-1) η(32z) η(48z)^2 η(64z)^(-1) η(96z)^2 η(192z)` at level 384. -/
abbrev cuspForm_384_eta_2m1_4p2_6p1_12m1_16m1_24m1_32p1_48p2_64m1_96p2_192p1 : gamma0CuspForms 384 :=
  etaQuotientCuspForm 384 sparse![384; 1 => -1, 3 => 2, 5 => 1, 11 => -1, 15 => -1, 23 => -1, 31 => 1, 47 => 2, 63 => -1, 95 => 2, 191 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_384_eta_2m1_4p2_6p1_12m1_16m1_24m1_32p1_48p2_64m1_96p2_192p1_first_coeffs :
    first_coeffs 100 cuspForm_384_eta_2m1_4p2_6p1_12m1_16m1_24m1_32p1_48p2_64m1_96p2_192p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1,
     0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0,
     0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, -1,
     0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -2, 0, -1, 0, 0, 0, 0,
     0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, -1, 0, -1] := by
  eta_coeff

end WeightTwoCusps
