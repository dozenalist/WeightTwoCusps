module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 192

The eta expression is `η(z)^(-2) η(2z)^4 η(3z)^2 η(4z)^(-2) η(6z)^(-2) η(8z) η(16z)^2 η(24z) η(32z)^(-1) η(48z)^2 η(96z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z)^2 η(4z)^(-2) η(6z)^(-2) η(8z) η(16z)^2 η(24z) η(32z)^(-1) η(48z)^2 η(96z)^(-1)` at level 192. -/
abbrev cuspForm_192_eta_1m2_2p4_3p2_4m2_6m2_8p1_16p2_24p1_32m1_48p2_96m1 : gamma0CuspForms 192 :=
  etaQuotientCuspForm 192 sparse![192; 0 => -2, 1 => 4, 2 => 2, 3 => -2, 5 => -2, 7 => 1, 15 => 2, 23 => 1, 31 => -1, 47 => 2, 95 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_192_eta_1m2_2p4_3p2_4m2_6m2_8p1_16p2_24p1_32m1_48p2_96m1_first_coeffs :
    first_coeffs 100 cuspForm_192_eta_1m2_2p4_3p2_4m2_6m2_8p1_16p2_24p1_32m1_48p2_96m1 =
    [0, 1, 2, 1, 0, 0, 2, 2, 0, 1, 0, 0, 0, 2, 4, 0, 0, -2, -2, 0,
     0, 2, -4, -4, 0, -1, 4, 1, 0, -4, -8, 2, 0, 0, -4, -4, 0, -2, 4, 2,
     0, -2, -4, 0, 0, 0, 0, -4, 0, 1, -2, -2, 0, -4, -10, -8, 0, 0, -8, -4,
     0, -2, -4, 2, 0, 0, 4, 4, 0, -4, 8, 12, 0, 2, -4, -1, 0, 8, 20, -6,
     0, 1, 12, 8, 0, 8, -4, -4, 0, 2, 8, 4, 0, 2, -8, 8, 0, -6, 2, 0] := by
  eta_coeff

end WeightTwoCusps
