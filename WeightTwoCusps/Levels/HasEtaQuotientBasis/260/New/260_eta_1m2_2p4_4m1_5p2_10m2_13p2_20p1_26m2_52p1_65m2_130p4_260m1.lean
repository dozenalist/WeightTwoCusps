module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 260

The eta expression is `η(z)^(-2) η(2z)^4 η(4z)^(-1) η(5z)^2 η(10z)^(-2) η(13z)^2 η(20z) η(26z)^(-2) η(52z) η(65z)^(-2) η(130z)^4 η(260z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(4z)^(-1) η(5z)^2 η(10z)^(-2) η(13z)^2 η(20z) η(26z)^(-2) η(52z) η(65z)^(-2) η(130z)^4 η(260z)^(-1)` at level 260. -/
abbrev cuspForm_260_eta_1m2_2p4_4m1_5p2_10m2_13p2_20p1_26m2_52p1_65m2_130p4_260m1 : gamma0CuspForms 260 :=
  etaQuotientCuspForm 260 sparse![260; 0 => -2, 1 => 4, 3 => -1, 4 => 2, 9 => -2, 12 => 2, 19 => 1, 25 => -2, 51 => 1, 64 => -2, 129 => 4, 259 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_260_eta_1m2_2p4_4m1_5p2_10m2_13p2_20p1_26m2_52p1_65m2_130p4_260m1_first_coeffs :
    first_coeffs 100 cuspForm_260_eta_1m2_2p4_4m1_5p2_10m2_13p2_20p1_26m2_52p1_65m2_130p4_260m1 =
    [0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 2, 3, 0, 0, 2, 0, 0, 4, 2, 1,
     2, -2, -2, -4, -4, 0, 0, -2, 2, 3, -6, -1, -2, -7, -2, 1, 2, 1, 6, 0,
     0, 0, -6, 0, -2, 1, 2, 3, 0, -4, -4, -10, 0, -6, -6, 3, -6, -3, 0, -1,
     -6, 1, 6, -1, 4, 0, 4, 1, -2, 9, 0, 3, 4, 7, 2, 0, 6, -10, 0, 4,
     2, 3, 4, 3, -6, 4, -8, -6, 2, -2, 10, 1, 2, 1, 2, 1, 4, 2, -6, 7] := by
  eta_coeff

end WeightTwoCusps
