module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 54

The eta expression is `η(z)^(-1) η(2z)^2 η(3z) η(18z) η(27z)^2 η(54z)^(-1)`; see
[the local level table](../../TABLE.md#level-54).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(3z) η(18z) η(27z)^2 η(54z)^(-1)` at level 54. -/
abbrev cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1 : gamma0CuspForms 54 :=
  etaQuotientCuspForm 54 sparse![54; 0 => -1, 1 => 2, 2 => 1, 17 => 1, 26 => 2, 53 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1_first_coeffs :
    first_coeffs 100 cuspForm_54_eta_1m1_2p2_3p1_18p1_27p2_54m1 =
    [0, 1, 1, 0, 0, -1, 0, -1, -1, 0, -2, 1, 0, -1, -1, 0, 2, 0, 0, -1,
     -1, 0, 2, 2, 0, 1, 2, 0, 0, -2, 0, 2, 3, 0, 0, 1, 0, 5, -4, 0,
     -2, 2, 0, -4, 1, 0, 4, -2, 0, -6, -2, 0, -6, -3, 0, -6, 1, 0, -4, -4,
     0, 5, -1, 0, -2, 4, 0, 11, 0, 0, 2, 0, 0, -7, 8, 0, 6, -1, 0, 11,
     -1, 0, 4, 1, 0, 0, 2, 0, 2, 6, 0, 1, 2, 0, -4, -2, 0, -7, -6, 0] := by
  eta_coeff

end WeightTwoCusps
