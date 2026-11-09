module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 390

The eta expression is `η(3z) η(5z)^2 η(10z)^(-1) η(13z) η(15z)^(-1) η(30z) η(65z)^(-1) η(130z) η(195z)^2 η(390z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(3z) η(5z)^2 η(10z)^(-1) η(13z) η(15z)^(-1) η(30z) η(65z)^(-1) η(130z) η(195z)^2 η(390z)^(-1)` at level 390. -/
abbrev cuspForm_390_eta_3p1_5p2_10m1_13p1_15m1_30p1_65m1_130p1_195p2_390m1 : gamma0CuspForms 390 :=
  etaQuotientCuspForm 390 sparse![390; 2 => 1, 4 => 2, 9 => -1, 12 => 1, 14 => -1, 29 => 1, 64 => -1, 129 => 1, 194 => 2, 389 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_390_eta_3p1_5p2_10m1_13p1_15m1_30p1_65m1_130p1_195p2_390m1_first_coeffs :
    first_coeffs 100 cuspForm_390_eta_3p1_5p2_10m1_13p1_15m1_30p1_65m1_130p1_195p2_390m1 =
    [0, 0, 0, 0, 1, 0, 0, -1, 0, -2, -1, 0, 2, 0, 0, 2, 0, -1, 0, 2,
     1, 0, 1, 1, -2, -2, 0, 0, -2, 0, -3, 0, -2, 1, 2, 3, 1, 1, -2, 0,
     -1, -2, 0, 2, 0, 0, 0, -2, 1, 0, 3, 0, 0, 1, 0, 0, 2, 2, -2, 0,
     0, 0, 0, 1, -1, 0, 1, 0, 0, 0, -2, -2, -2, -2, -4, -6, 0, 5, 0, 0,
     4, 0, 1, -2, 4, 1, -2, -2, 5, -4, 1, 0, 0, -2, 1, -2, 0, -1, 0, 6] := by
  eta_coeff

end WeightTwoCusps
