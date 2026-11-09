module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 260

The eta expression is `η(z)^(-3) η(2z)^8 η(4z)^(-3) η(13z) η(26z)^(-2) η(52z) η(65z)^(-2) η(130z)^6 η(260z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^8 η(4z)^(-3) η(13z) η(26z)^(-2) η(52z) η(65z)^(-2) η(130z)^6 η(260z)^(-2)` at level 260. -/
abbrev cuspForm_260_eta_1m3_2p8_4m3_13p1_26m2_52p1_65m2_130p6_260m2 : gamma0CuspForms 260 :=
  etaQuotientCuspForm 260 sparse![260; 0 => -3, 1 => 8, 3 => -3, 12 => 1, 25 => -2, 51 => 1, 64 => -2, 129 => 6, 259 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_260_eta_1m3_2p8_4m3_13p1_26m2_52p1_65m2_130p6_260m2_first_coeffs :
    first_coeffs 100 cuspForm_260_eta_1m3_2p8_4m3_13p1_26m2_52p1_65m2_130p6_260m2 =
    [0, 0, 0, 0, 0, 0, 1, 3, 1, -2, 2, 1, -4, -1, -2, 0, 2, -4, -1, -3,
     -5, 0, 2, 0, -3, 6, 1, -2, 1, -2, 6, 3, 8, 5, -2, -2, 0, 7, -8, -1,
     2, 2, 6, -6, -3, -7, -7, -3, 6, -4, -8, 12, 2, 2, -4, -8, 12, 7, 7, 9,
     0, -8, -2, 9, -14, -2, 2, -1, 10, -14, -5, -11, -10, 1, 6, 2, -13, 12, 1, -6,
     -4, -10, 4, 5, 10, 10, 5, -6, 4, 10, -12, -2, -2, 5, 10, -10, -5, -6, -14, -5] := by
  eta_coeff

end WeightTwoCusps
