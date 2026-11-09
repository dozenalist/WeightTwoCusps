module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 260

The eta expression is `η(z)^(-1) η(2z)^2 η(10z)^2 η(20z)^(-1) η(52z) η(65z)`; see
[the local level table](../../TABLE.md#level-260).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(10z)^2 η(20z)^(-1) η(52z) η(65z)` at level 260. -/
abbrev cuspForm_260_eta_1m1_2p2_10p2_20m1_52p1_65p1 : gamma0CuspForms 260 :=
  etaQuotientCuspForm 260 sparse![260; 0 => -1, 1 => 2, 9 => 2, 19 => -1, 51 => 1, 64 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_260_eta_1m1_2p2_10p2_20m1_52p1_65p1_first_coeffs :
    first_coeffs 100 cuspForm_260_eta_1m1_2p2_10p2_20m1_52p1_65p1 =
    [0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, -1, -2, 0, -2, 0,
     1, -2, 0, 0, 0, -2, 1, 0, 0, 0, -2, 0, 0, 1, 0, 0, -2, 0, 0, 0,
     0, 1, 0, -2, 0, 2, 2, 0, 2, 0, 1, 0, 0, 0, 0, 2, 0, -1, -1, 0,
     0, 0, 0, -1, 0, 0, 2, 1, 2, 0, -1, 0, -1, 3, 0, 0, -1, 2, -1, 0,
     1, 2, 2, 3, 0, -2, 2, 0, 2, 0, 4, -1, 0, -3, 0, 2, -1, -2, -5, 0] := by
  eta_coeff

end WeightTwoCusps
