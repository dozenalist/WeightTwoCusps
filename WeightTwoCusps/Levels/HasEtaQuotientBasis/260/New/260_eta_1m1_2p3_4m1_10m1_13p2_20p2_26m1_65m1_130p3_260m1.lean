module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 260

The eta expression is `η(z)^(-1) η(2z)^3 η(4z)^(-1) η(10z)^(-1) η(13z)^2 η(20z)^2 η(26z)^(-1) η(65z)^(-1) η(130z)^3 η(260z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^3 η(4z)^(-1) η(10z)^(-1) η(13z)^2 η(20z)^2 η(26z)^(-1) η(65z)^(-1) η(130z)^3 η(260z)^(-1)` at level 260. -/
abbrev cuspForm_260_eta_1m1_2p3_4m1_10m1_13p2_20p2_26m1_65m1_130p3_260m1 : gamma0CuspForms 260 :=
  etaQuotientCuspForm 260 sparse![260; 0 => -1, 1 => 3, 3 => -1, 9 => -1, 12 => 2, 19 => 2, 25 => -1, 64 => -1, 129 => 3, 259 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_260_eta_1m1_2p3_4m1_10m1_13p2_20p2_26m1_65m1_130p3_260m1_first_coeffs :
    first_coeffs 100 cuspForm_260_eta_1m1_2p3_4m1_10m1_13p2_20p2_26m1_65m1_130p3_260m1 =
    [0, 0, 0, 0, 1, 1, -1, 0, 0, -1, 0, -1, 0, 0, 1, 1, -2, -2, -2, 2,
     0, -1, 2, 0, 2, 0, 0, -2, -2, 5, 1, 0, 0, 0, 3, 1, 0, 0, 0, 0,
     1, -1, -2, -2, -1, 0, -1, -2, -2, 2, 0, 0, 0, -2, 1, -1, 3, 4, -2, 2,
     1, -3, -4, -2, 1, 0, 1, 4, -2, -1, 1, -3, 0, -4, -1, 0, -2, -2, 0, 4,
     1, 1, 0, -2, 5, -1, 2, 8, 0, 4, 1, 0, -2, -4, 3, 1, -1, 2, 0, 2] := by
  eta_coeff

end WeightTwoCusps
