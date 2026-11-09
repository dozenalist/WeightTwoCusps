module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 252

The eta expression is `η(z)^(-2) η(2z) η(3z)^6 η(6z)^(-2) η(9z)^(-2) η(18z) η(21z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z) η(3z)^6 η(6z)^(-2) η(9z)^(-2) η(18z) η(21z)^2` at level 252. -/
abbrev cuspForm_252_eta_1m2_2p1_3p6_6m2_9m2_18p1_21p2 : gamma0CuspForms 252 :=
  etaQuotientCuspForm 252 sparse![252; 0 => -2, 1 => 1, 2 => 6, 5 => -2, 8 => -2, 17 => 1, 20 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_252_eta_1m2_2p1_3p6_6m2_9m2_18p1_21p2_first_coeffs :
    first_coeffs 100 cuspForm_252_eta_1m2_2p1_3p6_6m2_9m2_18p1_21p2 =
    [0, 0, 1, 2, 4, 2, 2, 0, 3, 2, 0, 2, 2, 8, 1, 2, 0, 2, 4, 0,
     2, 0, 4, 2, -2, -8, -2, -2, 0, -4, -2, 8, -3, 0, -16, -2, -2, 0, 0, -6,
     8, -2, 0, -8, -6, -4, -4, -4, -2, 0, -5, -4, -16, 0, -10, -8, -1, -2, 12, -8,
     -6, -16, -4, 2, -4, -8, 0, 16, 2, -4, 0, 2, 0, -8, -2, 2, 16, 2, -2, -24,
     -2, 4, -8, 4, -4, 16, 8, 0, -12, -2, 0, 0, 2, 4, 24, -4, 10, 8, 1, -4] := by
  eta_coeff

end WeightTwoCusps
