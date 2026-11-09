module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 260

The eta expression is `η(2z)^(-1) η(4z)^2 η(5z) η(13z) η(65z)^(-2) η(130z)^5 η(260z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(2z)^(-1) η(4z)^2 η(5z) η(13z) η(65z)^(-2) η(130z)^5 η(260z)^(-2)` at level 260. -/
abbrev cuspForm_260_eta_2m1_4p2_5p1_13p1_65m2_130p5_260m2 : gamma0CuspForms 260 :=
  etaQuotientCuspForm 260 sparse![260; 1 => -1, 3 => 2, 4 => 1, 12 => 1, 64 => -2, 129 => 5, 259 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_260_eta_2m1_4p2_5p1_13p1_65m2_130p5_260m2_first_coeffs :
    first_coeffs 100 cuspForm_260_eta_2m1_4p2_5p1_13p1_65m2_130p5_260m2 =
    [0, 1, 0, 1, 0, 0, -1, 1, -1, 0, 0, -1, -1, 0, -1, 0, -1, -1, -1, 1,
     -1, 2, 0, -1, 1, 1, 0, -1, 1, -1, 1, 1, 2, -1, 0, 0, 1, 1, 3, 0,
     0, -2, 1, 2, 1, -1, 1, -1, 0, 1, 0, -2, 0, -1, 0, -1, 1, 1, -1, -1,
     0, -1, -1, -1, -2, 0, 5, -1, 3, -3, -1, -3, 2, -3, 1, 1, -3, -3, -1, -2,
     2, -4, -5, -5, 2, -2, 5, 1, -3, 4, 2, 1, -1, 5, -1, 2, 1, 4, 0, -1] := by
  eta_coeff

end WeightTwoCusps
