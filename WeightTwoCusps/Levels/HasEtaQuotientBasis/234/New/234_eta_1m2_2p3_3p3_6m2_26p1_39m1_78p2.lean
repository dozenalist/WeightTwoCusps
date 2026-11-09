module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 234

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^3 η(6z)^(-2) η(26z) η(39z)^(-1) η(78z)^2`; see
[the local level table](../../TABLE.md#level-234).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^3 η(6z)^(-2) η(26z) η(39z)^(-1) η(78z)^2` at level 234. -/
abbrev cuspForm_234_eta_1m2_2p3_3p3_6m2_26p1_39m1_78p2 : gamma0CuspForms 234 :=
  etaQuotientCuspForm 234 sparse![234; 0 => -2, 1 => 3, 2 => 3, 5 => -2, 25 => 1, 38 => -1, 77 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_234_eta_1m2_2p3_3p3_6m2_26p1_39m1_78p2_first_coeffs :
    first_coeffs 100 cuspForm_234_eta_1m2_2p3_3p3_6m2_26p1_39m1_78p2 =
    [0, 0, 0, 0, 0, 0, 1, 2, 2, 1, -1, 0, 0, 1, 1, -3, -2, -3, 1, 1,
     -2, 1, -3, -1, -1, -1, 0, -3, 1, 0, -2, 1, 0, 0, -3, -1, 1, -3, 1, -1,
     -1, 2, 5, 6, 0, -1, 6, 4, 3, 2, -2, 1, 1, 5, -2, -3, 0, 4, 0, -6,
     1, -5, 0, 3, 1, -1, -5, 5, 1, -2, -1, 0, -3, -8, 3, -1, 2, 5, -1, 0,
     -2, 7, 9, -4, -3, -1, 2, 0, 2, -2, -2, 0, -1, 4, -8, 1, 1, 0, -2, -2] := by
  eta_coeff

end WeightTwoCusps
