module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 48

The eta expression is `η(z)^(-2) η(2z)^4 η(3z)^2 η(6z)^(-2) η(12z)^2`; see
[the local level table](../../TABLE.md#level-48).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z)^2 η(6z)^(-2) η(12z)^2` at level 48. -/
abbrev cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2 : gamma0CuspForms 48 :=
  etaQuotientCuspForm 48 sparse![48; 0 => -2, 1 => 4, 2 => 2, 5 => -2, 11 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2_first_coeffs :
    first_coeffs 100 cuspForm_48_eta_1m2_2p4_3p2_6m2_12p2 =
    [0, 1, 2, 1, 0, -2, -2, 0, 0, 1, -4, -4, 0, -2, 0, -2, 0, 2, 2, 4,
     0, 0, 8, 8, 0, -1, -4, 1, 0, 6, 4, -8, 0, -4, 4, 0, 0, 6, -8, -2,
     0, -6, 0, -4, 0, -2, -16, 0, 0, -7, -2, 2, 0, -2, -2, 8, 0, 4, 12, -4,
     0, -2, 16, 0, 0, 4, -8, 4, 0, 8, 0, -8, 0, 10, 12, -1, 0, 0, 4, 8,
     0, 1, -12, 4, 0, -4, 8, 6, 0, -6, -4, 0, 0, -8, 0, -8, 0, 2, -14, -4] := by
  eta_coeff

end WeightTwoCusps
