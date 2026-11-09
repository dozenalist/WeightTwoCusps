module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 440

The eta expression is `η(2z) η(10z)^2 η(20z)^(-1) η(22z) η(110z)^2 η(220z)^(-1)`; see
[the local level table](../../TABLE.md#level-440).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z) η(10z)^2 η(20z)^(-1) η(22z) η(110z)^2 η(220z)^(-1)` at level 440. -/
abbrev cuspForm_440_eta_2p1_10p2_20m1_22p1_110p2_220m1 : gamma0CuspForms 440 :=
  etaQuotientCuspForm 440 sparse![440; 1 => 1, 9 => 2, 19 => -1, 21 => 1, 109 => 2, 219 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_440_eta_2p1_10p2_20m1_22p1_110p2_220m1_first_coeffs :
    first_coeffs 100 cuspForm_440_eta_2p1_10p2_20m1_22p1_110p2_220m1 =
    [0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 0, -1, 0, 2, 0, 3, 0, 0, 0, 0,
     0, -2, 0, -1, 0, -2, 0, 1, 0, 0, 0, -1, 0, 1, 0, 0, 0, -3, 0, 0,
     0, 4, 0, 0, 0, -2, 0, 4, 0, 1, 0, 2, 0, 2, 0, 1, 0, -4, 0, -3,
     0, 0, 0, -6, 0, 2, 0, 1, 0, 3, 0, -3, 0, -2, 0, 0, 0, 0, 0, -2,
     0, 1, 0, 0, 0, 0, 0, 4, 0, 1, 0, 0, 0, 7, 0, 0, 0, -1, 0, 0] := by
  eta_coeff

end WeightTwoCusps
