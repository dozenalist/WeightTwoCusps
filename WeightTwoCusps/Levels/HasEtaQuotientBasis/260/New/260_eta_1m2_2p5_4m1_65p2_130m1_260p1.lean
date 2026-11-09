module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 260

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-1) η(65z)^2 η(130z)^(-1) η(260z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-1) η(65z)^2 η(130z)^(-1) η(260z)` at level 260. -/
abbrev cuspForm_260_eta_1m2_2p5_4m1_65p2_130m1_260p1 : gamma0CuspForms 260 :=
  etaQuotientCuspForm 260 sparse![260; 0 => -2, 1 => 5, 3 => -1, 64 => 2, 129 => -1, 259 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_260_eta_1m2_2p5_4m1_65p2_130m1_260p1_first_coeffs :
    first_coeffs 100 cuspForm_260_eta_1m2_2p5_4m1_65p2_130m1_260p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 1, -2, 0, 0, -3,
     0, 0, 0, -2, -2, 0, 0, 2, -2, 0, 0, -1, 2, 0, 0, 0, 2, 0, 0, 1,
     2, 0, 0, 2, -2, 0, 0, 4, 2, 0, 0, -2, 0, 0, 0, 0, 2, 0, 0, -1,
     0, 0, 0, -2, 0, 0, 0, 2, -4, 0, 0, -1, -2, 0, 0, 0, -2, -4, 0, -2,
     -2, 4, 0, -2, 4, 0, 0, -2, 6, 4, 0, 0, -2, 4, 0, 0, -2, -4, 0, 1] := by
  eta_coeff

end WeightTwoCusps
