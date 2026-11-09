module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 260

The eta expression is `η(z)^(-1) η(2z)^3 η(4z)^(-1) η(5z)^(-2) η(10z)^5 η(13z)^(-1) η(20z)^(-2) η(26z)^3 η(52z)^(-1) η(130z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^3 η(4z)^(-1) η(5z)^(-2) η(10z)^5 η(13z)^(-1) η(20z)^(-2) η(26z)^3 η(52z)^(-1) η(130z)` at level 260. -/
abbrev cuspForm_260_eta_1m1_2p3_4m1_5m2_10p5_13m1_20m2_26p3_52m1_130p1 : gamma0CuspForms 260 :=
  etaQuotientCuspForm 260 sparse![260; 0 => -1, 1 => 3, 3 => -1, 4 => -2, 9 => 5, 12 => -1, 19 => -2, 25 => 3, 51 => -1, 129 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_260_eta_1m1_2p3_4m1_5m2_10p5_13m1_20m2_26p3_52m1_130p1_first_coeffs :
    first_coeffs 100 cuspForm_260_eta_1m1_2p3_4m1_5m2_10p5_13m1_20m2_26p3_52m1_130p1 =
    [0, 0, 0, 0, 0, 0, 1, 1, -1, 0, 0, 1, 2, -3, 0, 0, -2, 0, -3, 1,
     1, 0, 0, -2, 1, 2, 1, 2, -1, -2, 0, -5, 0, -1, 2, 0, -2, 1, -4, 7,
     2, 2, 2, 0, 1, 1, 1, -1, 2, 2, 2, -2, 0, -4, 4, 0, -2, 1, -3, 1,
     0, 4, -2, -5, 2, 4, -2, -3, -2, -2, -1, -3, -2, 3, 0, -2, -5, -2, -1, 2,
     0, -2, 2, 3, 2, 0, 5, 0, 4, 2, 0, -8, -2, -1, 0, 0, -1, -2, -2, 3] := by
  eta_coeff

end WeightTwoCusps
