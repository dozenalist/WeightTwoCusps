module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 260

The eta expression is `η(z)^(-1) η(2z)^3 η(4z)^(-1) η(5z)^(-1) η(10z)^3 η(13z) η(20z)^(-1) η(26z)^(-1) η(52z) η(65z) η(130z)^(-1) η(260z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^3 η(4z)^(-1) η(5z)^(-1) η(10z)^3 η(13z) η(20z)^(-1) η(26z)^(-1) η(52z) η(65z) η(130z)^(-1) η(260z)` at level 260. -/
abbrev cuspForm_260_eta_1m1_2p3_4m1_5m1_10p3_13p1_20m1_26m1_52p1_65p1_130m1_260p1 : gamma0CuspForms 260 :=
  etaQuotientCuspForm 260 sparse![260; 0 => -1, 1 => 3, 3 => -1, 4 => -1, 9 => 3, 12 => 1, 19 => -1, 25 => -1, 51 => 1, 64 => 1, 129 => -1, 259 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_260_eta_1m1_2p3_4m1_5m1_10p3_13p1_20m1_26m1_52p1_65p1_130m1_260p1_first_coeffs :
    first_coeffs 100 cuspForm_260_eta_1m1_2p3_4m1_5m1_10p3_13p1_20m1_26m1_52p1_65p1_130m1_260p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, -1, 0, 0, 0, 1, -2, 0, 0,
     -2, -1, -1, -1, -1, 3, 0, 0, 0, -1, 3, 0, 2, 2, 1, -1, 0, 2, -2, 0,
     1, 1, 0, -1, 0, -2, -2, 2, 2, -1, -3, 1, 1, -1, -1, -3, 2, 0, 0, 4,
     -1, -1, 0, 0, -2, -1, -1, -2, 2, -1, -2, -3, 0, 0, 4, 1, -3, 3, 0, 0,
     -1, -1, 3, 2, 1, 4, 1, 1, 0, 2, -6, -1, 0, 2, 4, -6, 0, -4, -4, -4] := by
  eta_coeff

end WeightTwoCusps
