module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 220

The eta expression is `η(z)^(-2) η(2z)^4 η(4z)^(-1) η(5z)^2 η(10z)^(-2) η(11z)^2 η(20z) η(22z)^(-2) η(44z) η(55z)^(-2) η(110z)^4 η(220z)^(-1)`; see
[the local level table](../../TABLE.md#level-220).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(4z)^(-1) η(5z)^2 η(10z)^(-2) η(11z)^2 η(20z) η(22z)^(-2) η(44z) η(55z)^(-2) η(110z)^4 η(220z)^(-1)` at level 220. -/
abbrev cuspForm_220_eta_1m2_2p4_4m1_5p2_10m2_11p2_20p1_22m2_44p1_55m2_110p4_220m1 : gamma0CuspForms 220 :=
  etaQuotientCuspForm 220 sparse![220; 0 => -2, 1 => 4, 3 => -1, 4 => 2, 9 => -2, 10 => 2, 19 => 1, 21 => -2, 43 => 1, 54 => -2, 109 => 4, 219 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_220_eta_1m2_2p4_4m1_5p2_10m2_11p2_20p1_22m2_44p1_55m2_110p4_220m1_first_coeffs :
    first_coeffs 100 cuspForm_220_eta_1m2_2p4_4m1_5p2_10m2_11p2_20p1_22m2_44p1_55m2_110p4_220m1 =
    [0, 0, 0, 0, 0, 0, 1, 2, 1, 2, 3, 0, 0, 2, 0, 0, 4, 0, -3, 2,
     -2, -6, 0, 2, -4, 0, 2, -6, 0, 2, -4, -2, 3, 0, -4, 2, 2, 2, 0, -4,
     -3, -4, -2, -4, 0, 2, 1, -2, -10, -2, 0, -2, -2, 2, 5, 0, -2, -2, 2, 4,
     2, -2, 3, 8, 6, 2, 1, 6, 2, -8, -6, 6, 7, 2, 5, 0, 0, -2, -4, -4,
     4, 12, -6, 0, 0, 0, 0, -6, 1, -2, -3, -4, 0, 2, 2, 2, -10, -8, 0, -2] := by
  eta_coeff

end WeightTwoCusps
