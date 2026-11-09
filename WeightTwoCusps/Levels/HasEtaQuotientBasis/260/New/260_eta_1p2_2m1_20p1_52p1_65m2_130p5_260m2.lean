module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 260

The eta expression is `η(z)^2 η(2z)^(-1) η(20z) η(52z) η(65z)^(-2) η(130z)^5 η(260z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z)^2 η(2z)^(-1) η(20z) η(52z) η(65z)^(-2) η(130z)^5 η(260z)^(-2)` at level 260. -/
abbrev cuspForm_260_eta_1p2_2m1_20p1_52p1_65m2_130p5_260m2 : gamma0CuspForms 260 :=
  etaQuotientCuspForm 260 sparse![260; 0 => 2, 1 => -1, 19 => 1, 51 => 1, 64 => -2, 129 => 5, 259 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_260_eta_1p2_2m1_20p1_52p1_65m2_130p5_260m2_first_coeffs :
    first_coeffs 100 cuspForm_260_eta_1p2_2m1_20p1_52p1_65m2_130p5_260m2 =
    [0, 0, 0, 1, -2, 0, 0, 2, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 2,
     0, 0, 0, -1, 2, 0, 0, -2, -2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, -1, 2, 0, 0, -2, 2, 0, 0, 0, 0, 0, 0, -1, 2, 0, 0, -6,
     0, 0, 0, 0, 2, 0, 0, 2, 4, -4, 0, -2, 6, 0, 0, 1, -2, -4, 0, 0,
     2, 0, 0, 0, 0, 0, 0, -2, -2, 4, 0, 0, -2, -4, 0, 1, -2, 4, 0, 2] := by
  eta_coeff

end WeightTwoCusps
