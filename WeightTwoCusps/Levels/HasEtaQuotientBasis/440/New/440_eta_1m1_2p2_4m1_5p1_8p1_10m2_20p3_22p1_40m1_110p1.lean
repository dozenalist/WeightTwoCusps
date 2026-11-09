module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 440

The eta expression is `η(z)^(-1) η(2z)^2 η(4z)^(-1) η(5z) η(8z) η(10z)^(-2) η(20z)^3 η(22z) η(40z)^(-1) η(110z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(4z)^(-1) η(5z) η(8z) η(10z)^(-2) η(20z)^3 η(22z) η(40z)^(-1) η(110z)` at level 440. -/
abbrev cuspForm_440_eta_1m1_2p2_4m1_5p1_8p1_10m2_20p3_22p1_40m1_110p1 : gamma0CuspForms 440 :=
  etaQuotientCuspForm 440 sparse![440; 0 => -1, 1 => 2, 3 => -1, 4 => 1, 7 => 1, 9 => -2, 19 => 3, 21 => 1, 39 => -1, 109 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_440_eta_1m1_2p2_4m1_5p1_8p1_10m2_20p3_22p1_40m1_110p1_first_coeffs :
    first_coeffs 100 cuspForm_440_eta_1m1_2p2_4m1_5p1_8p1_10m2_20p3_22p1_40m1_110p1 =
    [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 2, 1, 1, 2,
     2, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, -1, -1, 0, 0, -1, 0, 3, -2, 0,
     1, -2, -2, 1, 0, -1, 3, 1, 0, 1, -1, -2, -1, -1, -1, 0, 2, 0, 2, -2,
     -2, -2, -3, -1, -2, -1, 1, 1, -3, 0, 2, -3, -4, 1, -1, 0, 2, 0, -2, 2,
     -2, -4, 0, -1, -2, -1, 2, 0, -1, -1, -2, -2, -2, -1, -2, -2, 2, 2, -2, 0] := by
  eta_coeff

end WeightTwoCusps
