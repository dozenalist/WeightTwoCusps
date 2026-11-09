module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 192

The eta expression is `η(z)^(-2) η(2z)^4 η(3z)^2 η(4z)^(-3) η(6z)^(-2) η(8z)^4 η(12z) η(16z)^(-2) η(24z) η(32z)^2 η(64z)^(-1) η(96z)^(-1) η(192z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z)^2 η(4z)^(-3) η(6z)^(-2) η(8z)^4 η(12z) η(16z)^(-2) η(24z) η(32z)^2 η(64z)^(-1) η(96z)^(-1) η(192z)` at level 192. -/
abbrev cuspForm_192_eta_1m2_2p4_3p2_4m3_6m2_8p4_12p1_16m2_24p1_32p2_64m1_96m1_192p1 : gamma0CuspForms 192 :=
  etaQuotientCuspForm 192 sparse![192; 0 => -2, 1 => 4, 2 => 2, 3 => -3, 5 => -2, 7 => 4, 11 => 1, 15 => -2, 23 => 1, 31 => 2, 63 => -1, 95 => -1, 191 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_192_eta_1m2_2p4_3p2_4m3_6m2_8p4_12p1_16m2_24p1_32p2_64m1_96m1_192p1_first_coeffs :
    first_coeffs 100 cuspForm_192_eta_1m2_2p4_3p2_4m3_6m2_8p4_12p1_16m2_24p1_32p2_64m1_96m1_192p1 =
    [0, 0, 0, 0, 0, 1, 2, 1, 0, 1, 4, 3, 0, 0, 0, 1, 0, 2, 0, -3,
     0, 1, 4, 0, 0, 0, 0, 3, 0, -1, -4, -1, 0, -3, -8, -6, 0, -2, -4, -4,
     0, -6, -4, 3, 0, -1, -8, -2, 0, -4, 0, -6, 0, -5, -10, -2, 0, 3, -4, -3,
     0, 2, 8, 1, 0, 6, 8, 3, 0, -4, 0, 4, 0, 8, -8, 0, 0, 4, 20, -1,
     0, -2, 8, 9, 0, 6, 4, 7, 0, -8, 4, 6, 0, 3, 0, 2, 0, 0, 16, 3] := by
  eta_coeff

end WeightTwoCusps
