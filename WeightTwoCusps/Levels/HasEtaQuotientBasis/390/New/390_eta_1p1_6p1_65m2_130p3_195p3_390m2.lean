module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 390

The eta expression is `η(z) η(6z) η(65z)^(-2) η(130z)^3 η(195z)^3 η(390z)^(-2)`; see
[the local level table](../../TABLE.md#level-390).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(6z) η(65z)^(-2) η(130z)^3 η(195z)^3 η(390z)^(-2)` at level 390. -/
abbrev cuspForm_390_eta_1p1_6p1_65m2_130p3_195p3_390m2 : gamma0CuspForms 390 :=
  etaQuotientCuspForm 390 sparse![390; 0 => 1, 5 => 1, 64 => -2, 129 => 3, 194 => 3, 389 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_390_eta_1p1_6p1_65m2_130p3_195p3_390m2_first_coeffs :
    first_coeffs 100 cuspForm_390_eta_1p1_6p1_65m2_130p3_195p3_390m2 =
    [0, 0, 0, 1, -1, -1, 0, 0, 1, -1, 2, 1, 0, 0, -1, -2, 0, 1, -1, 0,
     -1, 1, -1, 0, 1, 1, 0, 1, 0, 1, 1, -1, 0, 1, -1, -2, 0, -1, 0, 0,
     1, -1, 0, -1, 1, 0, -1, -1, -1, 1, 2, 0, 1, 0, 1, 2, 0, -1, 0, 1,
     -1, 0, 0, 0, 0, 0, -2, 1, 1, -2, -2, 1, -1, 0, -2, 3, 3, 1, 0, -1,
     -7, 0, 1, -2, 1, -2, 3, -1, 0, 2, 4, 0, 3, -1, 3, 4, -1, -1, 1, -2] := by
  eta_coeff

end WeightTwoCusps
