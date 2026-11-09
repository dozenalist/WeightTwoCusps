module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 260

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(5z)^(-1) η(10z)^3 η(20z)^(-1) η(26z) η(65z)^(-1) η(130z)^3 η(260z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(5z)^(-1) η(10z)^3 η(20z)^(-1) η(26z) η(65z)^(-1) η(130z)^3 η(260z)^(-1)` at level 260. -/
abbrev cuspForm_260_eta_1m2_2p5_4m2_5m1_10p3_20m1_26p1_65m1_130p3_260m1 : gamma0CuspForms 260 :=
  etaQuotientCuspForm 260 sparse![260; 0 => -2, 1 => 5, 3 => -2, 4 => -1, 9 => 3, 19 => -1, 25 => 1, 64 => -1, 129 => 3, 259 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_260_eta_1m2_2p5_4m2_5m1_10p3_20m1_26p1_65m1_130p3_260m1_first_coeffs :
    first_coeffs 100 cuspForm_260_eta_1m2_2p5_4m2_5m1_10p3_20m1_26p1_65m1_130p3_260m1 =
    [0, 0, 0, 0, 1, 2, 0, 0, 2, 1, 2, 0, 0, 4, -1, -2, 0, 0, 0, 0,
     2, 0, 0, -2, 0, 2, 0, 0, 0, 1, -5, -2, 0, -2, 0, -1, -2, 0, -2, -7,
     1, 2, 0, -2, 0, 0, -2, 0, -2, 2, -2, -2, 0, 2, -2, -3, 3, -2, 2, 2,
     -4, -1, -2, -2, -1, -5, 1, 2, 0, 3, 2, 0, -2, 2, 3, 2, 2, -2, 0, -2,
     0, 1, 4, 2, -2, 6, -2, 0, -2, 0, 9, 7, 0, -2, 1, -3, -2, 0, -2, 0] := by
  eta_coeff

end WeightTwoCusps
