module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 110

The eta expression is `η(z) η(5z)^(-1) η(10z)^2 η(11z) η(55z)^(-1) η(110z)^2`; see
[the local level table](../../TABLE.md#level-110).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(5z)^(-1) η(10z)^2 η(11z) η(55z)^(-1) η(110z)^2` at level 110. -/
abbrev cuspForm_110_eta_1p1_5m1_10p2_11p1_55m1_110p2 : gamma0CuspForms 110 :=
  etaQuotientCuspForm 110 sparse![110; 0 => 1, 4 => -1, 9 => 2, 10 => 1, 54 => -1, 109 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_110_eta_1p1_5m1_10p2_11p1_55m1_110p2_first_coeffs :
    first_coeffs 100 cuspForm_110_eta_1p1_5m1_10p2_11p1_55m1_110p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 0, 0, 2, -1, 0, 0, 0, 1, -1,
     1, 1, 0, 0, -3, -1, 0, 0, 0, -1, 1, 1, 1, 0, 1, -1, 3, 0, 0, 0,
     -2, -2, 0, 0, 0, 1, 1, 2, -2, 1, -1, 1, -2, -2, 0, 0, -3, 0, 0, 2,
     -1, 1, 1, 2, 2, 0, 0, -2, 4, -2, 2, -1, 1, 0, 0, 1, -1, 0, -2, -4,
     -1, 0, 0, 0, 1, 1, -2, -2, 1, 5, 1, 0, 0, -2, 0, 0, -1, 0, -2, -1] := by
  eta_coeff

end WeightTwoCusps
