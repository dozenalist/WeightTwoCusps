module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 112

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(8z)^2 η(16z)^(-1) η(56z) η(112z)`; see
[the local level table](../../TABLE.md#level-112).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(8z)^2 η(16z)^(-1) η(56z) η(112z)` at level 112. -/
abbrev cuspForm_112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1 : gamma0CuspForms 112 :=
  etaQuotientCuspForm 112 sparse![112; 0 => -2, 1 => 5, 3 => -2, 7 => 2, 15 => -1, 55 => 1, 111 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1_first_coeffs :
    first_coeffs 100 cuspForm_112_eta_1m2_2p5_4m2_8p2_16m1_56p1_112p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, -2, -2, 0, 0, -4,
     0, 0, 0, 2, -4, 0, 0, 0, 0, 0, 0, -4, 2, 0, 0, 0, 0, 0, 0, 2,
     0, 0, 0, 6, 0, 0, 0, 0, 4, 0, 0, -4, 0, 0, 0, 4, 2, 0, 0, 0,
     0, 0, 0, -1, -2, 0, 0, -2, 0, 0, 0, 4, 2, 0, 0, 8, 0, 0, 0, -8,
     0, 0, 0, -4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, -6, -4, 0, 0, -6] := by
  eta_coeff

end WeightTwoCusps
