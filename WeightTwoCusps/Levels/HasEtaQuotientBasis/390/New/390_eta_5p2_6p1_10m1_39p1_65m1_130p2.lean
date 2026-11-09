module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 390

The eta expression is `η(5z)^2 η(6z) η(10z)^(-1) η(39z) η(65z)^(-1) η(130z)^2`; see
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

/-- The cuspidal eta quotient `η(5z)^2 η(6z) η(10z)^(-1) η(39z) η(65z)^(-1) η(130z)^2` at level 390. -/
abbrev cuspForm_390_eta_5p2_6p1_10m1_39p1_65m1_130p2 : gamma0CuspForms 390 :=
  etaQuotientCuspForm 390 sparse![390; 4 => 2, 5 => 1, 9 => -1, 38 => 1, 64 => -1, 129 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_390_eta_5p2_6p1_10m1_39p1_65m1_130p2_first_coeffs :
    first_coeffs 100 cuspForm_390_eta_5p2_6p1_10m1_39p1_65m1_130p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -2, -1, 0, 0, 0,
     0, 2, -1, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, -2, 0, 0, 0,
     1, 0, -2, 0, 0, -2, 0, 0, 0, -1, 0, 0, 1, 0, 2, -1, 0, -2, 0, 0,
     0, 3, 0, 0, 0, 0, -2, 2, 0, -2, 0, 0, 2, 0, 0, 3, 0, 0, 0, -1,
     -2, 1, -1, 0, 2, -2, 2, 1, -1, 0, 2, -1, 2, 2, 3, 2, 0, -2, 0, -4] := by
  eta_coeff

end WeightTwoCusps
