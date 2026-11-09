module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-4) η(2z)^10 η(3z)^2 η(4z)^(-4) η(6z)^(-4) η(12z)^2 η(21z)^(-2) η(42z)^6 η(84z)^(-2)`; see
[the local level table](../../TABLE.md#level-252).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^10 η(3z)^2 η(4z)^(-4) η(6z)^(-4) η(12z)^2 η(21z)^(-2) η(42z)^6 η(84z)^(-2)` at level 252. -/
abbrev cuspForm_252_eta_1m4_2p10_3p2_4m4_6m4_12p2_21m2_42p6_84m2 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -4, 1 => 10, 2 => 2, 3 => -4, 5 => -4, 11 => 2, 20 => -2, 41 => 6, 83 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m4_2p10_3p2_4m4_6m4_12p2_21m2_42p6_84m2_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m4_2p10_3p2_4m4_6m4_12p2_21m2_42p6_84m2 =
    [0, 0, 1, 4, 4, -2, -4, 0, 3, 4, 0, -2, -4, -8, 1, 4, 0, -2, -8, 0,
     2, 0, 4, -2, 4, 8, -2, -4, 0, 4, 4, -8, -3, 0, -16, 2, 4, 0, 0, -12,
     8, 2, 0, 8, -6, -8, -4, 4, 4, 0, -5, -8, -16, 0, 20, 8, -1, -4, 12, 8,
     12, 16, -4, 4, -4, 8, 0, -16, 2, -8, 0, -2, 0, 8, -2, 4, 16, -2, 4, 24,
     -2, 8, -8, -4, 8, -16, 8, 0, -12, 2, 0, 0, 2, 8, 24, 4, -20, -8, 1, -8] := by
  eta_coeff

end WeightTwoCusps
