module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 390

The eta expression is `η(z) η(2z)^(-1) η(6z) η(10z) η(13z) η(15z) η(30z)^(-1) η(39z)^(-1) η(65z)^(-1) η(78z) η(130z) η(195z)`; see
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

/-- The cuspidal eta quotient `η(z) η(2z)^(-1) η(6z) η(10z) η(13z) η(15z) η(30z)^(-1) η(39z)^(-1) η(65z)^(-1) η(78z) η(130z) η(195z)` at level 390. -/
abbrev cuspForm_390_eta_1p1_2m1_6p1_10p1_13p1_15p1_30m1_39m1_65m1_78p1_130p1_195p1 : gamma0CuspForms 390 :=
  etaQuotientCuspForm 390 sparse![390; 0 => 1, 1 => -1, 5 => 1, 9 => 1, 12 => 1, 14 => 1, 29 => -1, 38 => -1, 64 => -1, 77 => 1, 129 => 1, 194 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_390_eta_1p1_2m1_6p1_10p1_13p1_15p1_30m1_39m1_65m1_78p1_130p1_195p1_first_coeffs :
    first_coeffs 100 cuspForm_390_eta_1p1_2m1_6p1_10p1_13p1_15p1_30m1_39m1_65m1_78p1_130p1_195p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, -1, 1, -1, 0,
     0, 2, -1, 0, 0, 1, -1, 1, -1, 4, -3, 1, -2, 1, -2, 1, -2, 2, -2, -1,
     0, 1, -2, 1, -1, 6, -1, -2, 1, 3, -2, 0, 1, 2, 1, -4, 3, 1, -3, -1,
     0, 2, 0, -2, 0, -1, -2, -1, 4, -3, 1, -5, 1, 1, -4, -2, 2, 5, 1, -2,
     1, -2, 1, -1, 7, 1, 3, -2, 3, 0, -1, 0, 3, 2, 0, 0, 2, -7, -3, -3] := by
  eta_coeff

end WeightTwoCusps
