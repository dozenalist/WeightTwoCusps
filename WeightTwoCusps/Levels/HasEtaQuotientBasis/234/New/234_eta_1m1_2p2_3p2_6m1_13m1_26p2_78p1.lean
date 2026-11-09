module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 234

The eta expression is `η(z)^(-1) η(2z)^2 η(3z)^2 η(6z)^(-1) η(13z)^(-1) η(26z)^2 η(78z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(3z)^2 η(6z)^(-1) η(13z)^(-1) η(26z)^2 η(78z)` at level 234. -/
abbrev cuspForm_234_eta_1m1_2p2_3p2_6m1_13m1_26p2_78p1 : gamma0CuspForms 234 :=
  etaQuotientCuspForm 234 sparse![234; 0 => -1, 1 => 2, 2 => 2, 5 => -1, 12 => -1, 25 => 2, 77 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_234_eta_1m1_2p2_3p2_6m1_13m1_26p2_78p1_first_coeffs :
    first_coeffs 100 cuspForm_234_eta_1m1_2p2_3p2_6m1_13m1_26p2_78p1 =
    [0, 0, 0, 0, 0, 1, 1, 0, -1, -2, 0, -1, 0, 0, -2, 1, 0, 2, 1, 1,
     3, -1, -2, 0, -1, 0, 1, 0, 1, -2, 2, 0, 0, 2, 0, -2, -2, 0, 0, 1,
     2, 1, -4, 0, -1, 3, -1, -3, -4, -2, 0, 0, 0, -2, 4, -2, 4, -2, 2, 5,
     -3, 0, 2, 1, 0, 1, 2, 2, -2, 2, 0, 1, 3, -1, -2, 0, 0, -2, 0, 0,
     -1, -2, 0, -1, 3, 2, -6, -2, 0, 3, -4, 0, 0, 0, 0, 2, 1, -1, 2, -6] := by
  eta_coeff

end WeightTwoCusps
