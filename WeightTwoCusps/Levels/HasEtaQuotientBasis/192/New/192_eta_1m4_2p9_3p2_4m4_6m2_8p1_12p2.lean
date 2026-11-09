module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 192

The eta expression is `η(z)^(-4) η(2z)^9 η(3z)^2 η(4z)^(-4) η(6z)^(-2) η(8z) η(12z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^9 η(3z)^2 η(4z)^(-4) η(6z)^(-2) η(8z) η(12z)^2` at level 192. -/
abbrev cuspForm_192_eta_1m4_2p9_3p2_4m4_6m2_8p1_12p2 : gamma0CuspForms 192 :=
  etaQuotientCuspForm 192 sparse![192; 0 => -4, 1 => 9, 2 => 2, 3 => -4, 5 => -2, 7 => 1, 11 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_192_eta_1m4_2p9_3p2_4m4_6m2_8p1_12p2_first_coeffs :
    first_coeffs 100 cuspForm_192_eta_1m4_2p9_3p2_4m4_6m2_8p1_12p2 =
    [0, 1, 4, 5, 2, 2, 6, 8, 4, 1, 8, 8, 2, 2, 0, 2, 0, 2, 4, -8,
     -4, 0, 0, 0, -4, -1, -8, -7, 0, -6, -12, -8, 0, -4, -24, -16, 2, -6, 0, -14,
     -8, -6, -16, 8, -8, 2, 0, -16, 0, -7, -4, -6, -4, 2, -18, -16, 0, 4, 8, -8,
     -4, 2, 0, 8, 0, 4, 16, 8, 4, -8, 0, 32, 4, 10, -8, -5, 8, 0, 36, -8,
     0, 1, 8, 24, 0, 4, 0, 26, 16, -6, 8, 16, 16, 8, 0, 16, 0, 2, 36, 8] := by
  eta_coeff

end WeightTwoCusps
