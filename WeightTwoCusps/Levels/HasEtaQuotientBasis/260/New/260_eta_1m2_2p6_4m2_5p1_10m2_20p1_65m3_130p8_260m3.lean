module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 260

The eta expression is `η(z)^(-2) η(2z)^6 η(4z)^(-2) η(5z) η(10z)^(-2) η(20z) η(65z)^(-3) η(130z)^8 η(260z)^(-3)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^6 η(4z)^(-2) η(5z) η(10z)^(-2) η(20z) η(65z)^(-3) η(130z)^8 η(260z)^(-3)` at level 260. -/
abbrev cuspForm_260_eta_1m2_2p6_4m2_5p1_10m2_20p1_65m3_130p8_260m3 : gamma0CuspForms 260 :=
  etaQuotientCuspForm 260 sparse![260; 0 => -2, 1 => 6, 3 => -2, 4 => 1, 9 => -2, 19 => 1, 64 => -3, 129 => 8, 259 => -3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_260_eta_1m2_2p6_4m2_5p1_10m2_20p1_65m3_130p8_260m3_first_coeffs :
    first_coeffs 100 cuspForm_260_eta_1m2_2p6_4m2_5p1_10m2_20p1_65m3_130p8_260m3 =
    [0, 0, 0, 1, 2, -1, -2, 1, -3, -4, 1, 0, 1, 4, 4, -1, -2, 2, -3, -4,
     2, 4, -1, 3, 6, -2, 0, -2, -5, -6, 1, 2, -4, 7, 6, -2, -4, -1, -7, -8,
     3, 2, 0, 5, 8, -2, -2, 3, -5, -10, 4, 8, -1, 8, 10, -3, -2, 1, -11, -10,
     3, 4, -1, 11, 12, -4, -6, 3, -8, -10, 1, -4, 4, 1, 2, -1, -6, 4, 0, -4,
     3, 2, 0, 7, 6, 0, 4, -4, -7, 2, -1, 8, -11, -1, 4, -5, -4, -8, 6, -6] := by
  eta_coeff

end WeightTwoCusps
