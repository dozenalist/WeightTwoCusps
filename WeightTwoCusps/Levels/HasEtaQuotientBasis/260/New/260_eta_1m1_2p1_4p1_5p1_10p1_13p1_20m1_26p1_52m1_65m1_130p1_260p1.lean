module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 260

The eta expression is `η(z)^(-1) η(2z) η(4z) η(5z) η(10z) η(13z) η(20z)^(-1) η(26z) η(52z)^(-1) η(65z)^(-1) η(130z) η(260z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(4z) η(5z) η(10z) η(13z) η(20z)^(-1) η(26z) η(52z)^(-1) η(65z)^(-1) η(130z) η(260z)` at level 260. -/
abbrev cuspForm_260_eta_1m1_2p1_4p1_5p1_10p1_13p1_20m1_26p1_52m1_65m1_130p1_260p1 : gamma0CuspForms 260 :=
  etaQuotientCuspForm 260 sparse![260; 0 => -1, 1 => 1, 3 => 1, 4 => 1, 9 => 1, 12 => 1, 19 => -1, 25 => 1, 51 => -1, 64 => -1, 129 => 1, 259 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_260_eta_1m1_2p1_4p1_5p1_10p1_13p1_20m1_26p1_52m1_65m1_130p1_260p1_first_coeffs :
    first_coeffs 100 cuspForm_260_eta_1m1_2p1_4p1_5p1_10p1_13p1_20m1_26p1_52m1_65m1_130p1_260p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 1, 1, 2,
     2, 1, 3, 1, 0, 2, -1, 1, 1, -1, -1, 2, -2, -1, 3, -3, 1, 2, -1, -2,
     0, -2, -3, 0, -5, -3, -5, -6, -4, -1, -2, -5, 1, -6, -3, 2, 1, -5, 4, 2,
     -5, 3, -3, -3, 0, 1, -6, 1, -5, -3, 4, -1, 1, 5, -1, -6, 7, 4, 2, 6,
     0, -1, 2, 7, -3, 4, 0, 2, 3, -6, 4, -2, 7, -3, 9, -4, 4, 0, -3, 6] := by
  eta_coeff

end WeightTwoCusps
