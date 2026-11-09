module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 300

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(10z)^(-1) η(15z) η(20z)^2 η(75z)`; see
[the local level table](../../TABLE.md#level-300).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(10z)^(-1) η(15z) η(20z)^2 η(75z)` at level 300. -/
abbrev cuspForm_300_eta_1m2_2p5_4m2_10m1_15p1_20p2_75p1 : gamma0CuspForms 300 :=
  etaQuotientCuspForm 300 sparse![300; 0 => -2, 1 => 5, 3 => -2, 9 => -1, 14 => 1, 19 => 2, 74 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_300_eta_1m2_2p5_4m2_10m1_15p1_20p2_75p1_first_coeffs :
    first_coeffs 100 cuspForm_300_eta_1m2_2p5_4m2_10m1_15p1_20p2_75p1 =
    [0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 2, 1, 2, 0, 0, 2,
     -1, 0, 0, 0, 0, 0, 0, 0, 0, -2, 1, 0, 0, 0, -2, 0, -2, 0, 0, -2,
     2, 2, 0, 0, 0, -3, -4, 0, 0, -2, -1, 0, 0, 0, -2, -2, -2, 0, 0, -2,
     0, -2, 0, 0, 2, 0, -4, 0, 0, 0, -2, 0, 0, 0, 0, -2, 0, 0, 0, 0,
     -1, -4, 0, 0, -4, 0, 0, 0, 0, -2, 0, 0, 0, 0, -4, 0, 0, 0, 0, -2] := by
  eta_coeff

end WeightTwoCusps
