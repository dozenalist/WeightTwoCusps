module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 192

The eta expression is `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-4) η(6z)^(-1) η(8z)^3 η(12z)^2 η(16z)^(-1) η(24z)^(-1) η(48z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^7 η(3z) η(4z)^(-4) η(6z)^(-1) η(8z)^3 η(12z)^2 η(16z)^(-1) η(24z)^(-1) η(48z)` at level 192. -/
abbrev cuspForm_192_eta_1m3_2p7_3p1_4m4_6m1_8p3_12p2_16m1_24m1_48p1 : gamma0CuspForms 192 :=
  etaQuotientCuspForm 192 sparse![192; 0 => -3, 1 => 7, 2 => 1, 3 => -4, 5 => -1, 7 => 3, 11 => 2, 15 => -1, 23 => -1, 47 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_192_eta_1m3_2p7_3p1_4m4_6m1_8p3_12p2_16m1_24m1_48p1_first_coeffs :
    first_coeffs 100 cuspForm_192_eta_1m3_2p7_3p1_4m4_6m1_8p3_12p2_16m1_24m1_48p1 =
    [0, 0, 1, 3, 2, 0, 3, 6, 4, 0, 2, 6, 2, 0, 0, 0, 0, 0, 1, -6,
     -4, 0, 0, 0, -4, 0, -2, -3, 0, 0, -6, -6, 0, 0, -6, -12, 2, 0, 0, -6,
     -8, 0, -4, 6, -8, 0, 0, -12, 0, 0, -1, -6, -4, 0, -9, -12, 0, 0, 2, -6,
     -4, 0, 0, 6, 0, 0, 4, 6, 4, 0, 0, 24, 4, 0, -2, -3, 8, 0, 18, -6,
     0, 0, 2, 18, 0, 0, 0, 12, 16, 0, 2, 12, 16, 0, 0, 12, 0, 0, 9, 6] := by
  eta_coeff

end WeightTwoCusps
