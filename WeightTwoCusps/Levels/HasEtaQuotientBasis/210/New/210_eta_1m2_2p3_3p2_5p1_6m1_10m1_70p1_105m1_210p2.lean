module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 210

The eta expression is `η(z)^(-2) η(2z)^3 η(3z)^2 η(5z) η(6z)^(-1) η(10z)^(-1) η(70z) η(105z)^(-1) η(210z)^2`; see
[the local level table](../../TABLE.md#level-210).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(3z)^2 η(5z) η(6z)^(-1) η(10z)^(-1) η(70z) η(105z)^(-1) η(210z)^2` at level 210. -/
abbrev cuspForm_210_eta_1m2_2p3_3p2_5p1_6m1_10m1_70p1_105m1_210p2 : gamma0CuspForms 210 :=
  etaQuotientCuspForm 210 sparse![210; 0 => -2, 1 => 3, 2 => 2, 4 => 1, 5 => -1, 9 => -1, 69 => 1, 104 => -1, 209 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_210_eta_1m2_2p3_3p2_5p1_6m1_10m1_70p1_105m1_210p2_first_coeffs :
    first_coeffs 100 cuspForm_210_eta_1m2_2p3_3p2_5p1_6m1_10m1_70p1_105m1_210p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 2, 2,
     1, 1, 0, 0, 1, -1, 0, 0, 0, -1, 0, 1, -2, -2, -2, -1, -4, 0, 2, -1,
     1, 0, -2, -4, 0, 1, -3, -2, 0, -2, -1, 2, 2, -4, -1, -1, -3, 2, 2, 2,
     0, 3, -2, -2, -2, 0, -1, -2, 4, -2, 2, 3, 0, 0, 1, -2, -4, 2, 4, 4,
     1, 2, 0, -2, 2, -1, -2, 0, 0, -2, 0, 2, 0, -4, 1, 1, 1, 2, 2, 2] := by
  eta_coeff

end WeightTwoCusps
