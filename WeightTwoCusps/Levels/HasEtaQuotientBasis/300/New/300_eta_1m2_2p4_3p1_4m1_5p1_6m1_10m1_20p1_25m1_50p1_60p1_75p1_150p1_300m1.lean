module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 300

The eta expression is `η(z)^(-2) η(2z)^4 η(3z) η(4z)^(-1) η(5z) η(6z)^(-1) η(10z)^(-1) η(20z) η(25z)^(-1) η(50z) η(60z) η(75z) η(150z) η(300z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^4 η(3z) η(4z)^(-1) η(5z) η(6z)^(-1) η(10z)^(-1) η(20z) η(25z)^(-1) η(50z) η(60z) η(75z) η(150z) η(300z)^(-1)` at level 300. -/
abbrev cuspForm_300_eta_1m2_2p4_3p1_4m1_5p1_6m1_10m1_20p1_25m1_50p1_60p1_75p1_150p1_300m1 : gamma0CuspForms 300 :=
  etaQuotientCuspForm 300 sparse![300; 0 => -2, 1 => 4, 2 => 1, 3 => -1, 4 => 1, 5 => -1, 9 => -1, 19 => 1, 24 => -1, 49 => 1, 59 => 1, 74 => 1, 149 => 1, 299 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_300_eta_1m2_2p4_3p1_4m1_5p1_6m1_10m1_20p1_25m1_50p1_60p1_75p1_150p1_300m1_first_coeffs :
    first_coeffs 100 cuspForm_300_eta_1m2_2p4_3p1_4m1_5p1_6m1_10m1_20p1_25m1_50p1_60p1_75p1_150p1_300m1 =
    [0, 1, 2, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, -2, 0, 0,
     -1, -1, -2, 1, -1, 0, 1, 1, 1, 0, 1, -1, -1, -1, 0, 0, 0, 3, 0, -1,
     2, 0, -3, -3, -1, -3, -2, -1, 0, -1, -1, 2, 0, 2, 1, -2, -3, 0, -1, 1,
     0, -1, 2, -3, -1, 0, 0, -2, -4, -3, -2, -1, -2, 1, 0, -2, 0, 1, 3, 1,
     -1, -1, -1, -2, 1, 0, 1, 3, 0, -1, 0, 0, -1, -2, -4, 0, -1, -1, 0, 1] := by
  eta_coeff

end WeightTwoCusps
