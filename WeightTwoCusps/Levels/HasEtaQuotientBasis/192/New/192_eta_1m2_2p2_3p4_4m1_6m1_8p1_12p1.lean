module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 192

The eta expression is `η(z)^(-2) η(2z)^2 η(3z)^4 η(4z)^(-1) η(6z)^(-1) η(8z) η(12z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^2 η(3z)^4 η(4z)^(-1) η(6z)^(-1) η(8z) η(12z)` at level 192. -/
abbrev cuspForm_192_eta_1m2_2p2_3p4_4m1_6m1_8p1_12p1 : gamma0CuspForms 192 :=
  etaQuotientCuspForm 192 sparse![192; 0 => -2, 1 => 2, 2 => 4, 3 => -1, 5 => -1, 7 => 1, 11 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_192_eta_1m2_2p2_3p4_4m1_6m1_8p1_12p1_first_coeffs :
    first_coeffs 100 cuspForm_192_eta_1m2_2p2_3p4_4m1_6m1_8p1_12p1 =
    [0, 1, 2, 3, 2, 2, 4, 4, 4, 1, 4, 4, 2, 2, 0, 2, 0, 2, 2, -4,
     -4, 0, 0, 0, -4, -1, -4, -5, 0, -6, -8, -4, 0, -4, -12, -8, 2, -6, 0, -10,
     -8, -6, -8, 4, -8, 2, 0, -8, 0, -7, -2, -2, -4, 2, -12, -8, 0, 4, 4, -4,
     -4, 2, 0, 4, 0, 4, 8, 4, 4, -8, 0, 16, 4, 10, -4, -3, 8, 0, 24, -4,
     0, 1, 4, 12, 0, 4, 0, 18, 16, -6, 4, 8, 16, 8, 0, 8, 0, 2, 18, 4] := by
  eta_coeff

end WeightTwoCusps
