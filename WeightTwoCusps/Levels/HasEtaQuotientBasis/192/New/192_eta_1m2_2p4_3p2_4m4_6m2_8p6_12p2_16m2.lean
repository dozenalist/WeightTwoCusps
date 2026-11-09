module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 192

The eta expression is `η(z)^(-2) η(2z)^4 η(3z)^2 η(4z)^(-4) η(6z)^(-2) η(8z)^6 η(12z)^2 η(16z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z)^2 η(4z)^(-4) η(6z)^(-2) η(8z)^6 η(12z)^2 η(16z)^(-2)` at level 192. -/
abbrev cuspForm_192_eta_1m2_2p4_3p2_4m4_6m2_8p6_12p2_16m2 : gamma0CuspForms 192 :=
  etaQuotientCuspForm 192 sparse![192; 0 => -2, 1 => 4, 2 => 2, 3 => -4, 5 => -2, 7 => 6, 11 => 2, 15 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_192_eta_1m2_2p4_3p2_4m4_6m2_8p6_12p2_16m2_first_coeffs :
    first_coeffs 100 cuspForm_192_eta_1m2_2p4_3p2_4m4_6m2_8p6_12p2_16m2 =
    [0, 1, 2, 1, 0, 2, 6, 4, 0, 1, 4, 4, 0, 2, 0, -2, 0, 2, 2, -4,
     0, 0, 0, 0, 0, -1, -4, 1, 0, -6, -12, -4, 0, -4, -12, -8, 0, -6, 0, 2,
     0, -6, -8, 4, 0, 2, 0, -8, 0, -7, -2, -6, 0, 2, -18, -8, 0, 4, 4, -4,
     0, 2, 0, 4, 0, 4, 8, 4, 0, -8, 0, 16, 0, 10, -4, -1, 0, 0, 36, -4,
     0, 1, 4, 12, 0, 4, 0, -2, 0, -6, 4, 8, 0, 8, 0, 8, 0, 2, 18, 4] := by
  eta_coeff

end WeightTwoCusps
