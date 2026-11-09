module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 390

The eta expression is `η(z)^(-1) η(2z) η(3z)^2 η(6z)^(-1) η(10z) η(13z) η(195z)^2 η(390z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z)^2 η(6z)^(-1) η(10z) η(13z) η(195z)^2 η(390z)^(-1)` at level 390. -/
abbrev cuspForm_390_eta_1m1_2p1_3p2_6m1_10p1_13p1_195p2_390m1 : gamma0CuspForms 390 :=
  etaQuotientCuspForm 390 sparse![390; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 9 => 1, 12 => 1, 194 => 2, 389 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_390_eta_1m1_2p1_3p2_6m1_10p1_13p1_195p2_390m1_first_coeffs :
    first_coeffs 100 cuspForm_390_eta_1m1_2p1_3p2_6m1_10p1_13p1_195p2_390m1 =
    [0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, -1, -1, 0, -1, -1, -1, 0, -1, -1,
     0, -2, -1, -1, 1, 1, -2, 0, -2, -1, 0, 1, -1, -2, 0, 1, 1, 0, 1, 2,
     -1, 2, 0, -1, 1, 0, 1, 0, 1, 1, 1, 0, 4, 0, 0, 0, 1, 0, 2, 3,
     1, -1, -1, 2, 0, -2, 1, 0, 0, 1, 0, 1, 1, 4, 1, 1, -1, 0, -1, -2,
     0, 0, 0, 0, -4, 0, -1, 0, -1, -2, -1, -3, 1, 2, 3, 0, -1, 0, -3, -3] := by
  eta_coeff

end WeightTwoCusps
