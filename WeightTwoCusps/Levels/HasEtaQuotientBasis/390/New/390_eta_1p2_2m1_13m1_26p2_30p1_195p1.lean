module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 390

The eta expression is `η(z)^2 η(2z)^(-1) η(13z)^(-1) η(26z)^2 η(30z) η(195z)`; see
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

/-- The cuspidal eta quotient `η(z)^2 η(2z)^(-1) η(13z)^(-1) η(26z)^2 η(30z) η(195z)` at level 390. -/
abbrev cuspForm_390_eta_1p2_2m1_13m1_26p2_30p1_195p1 : gamma0CuspForms 390 :=
  etaQuotientCuspForm 390 sparse![390; 0 => 2, 1 => -1, 12 => -1, 25 => 2, 29 => 1, 194 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_390_eta_1p2_2m1_13m1_26p2_30p1_195p1_first_coeffs :
    first_coeffs 100 cuspForm_390_eta_1p2_2m1_13m1_26p2_30p1_195p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0, 2, 0, 0, 0, 0,
     -2, 0, 0, 0, 1, -2, 0, 2, 2, 0, 0, 0, 0, -2, 0, 0, -2, 0, 0, 0,
     2, -1, 2, 0, 0, -2, 0, 2, 0, -2, 3, -2, 0, 0, 1, 2, 0, -2, -2, -2,
     0, 0, 0, 2, 0, 0, 4, 0, 0, 0, -2, -1, 2, -2, 0, -2, 0, -2, 0, 2,
     1, 2, 0, 0, -3, 2, 2, -2, 0, 3, -2, 0, -2, 4, 0, 0, 0, 0, -2, -2] := by
  eta_coeff

end WeightTwoCusps
