module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 162

The eta expression is `η(z)^(-1) η(2z)^2 η(3z) η(6z)^(-1) η(18z) η(27z)^2`; see
[the local level table](../../TABLE.md#level-162).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(3z) η(6z)^(-1) η(18z) η(27z)^2` at level 162. -/
abbrev cuspForm_162_eta_1m1_2p2_3p1_6m1_18p1_27p2 : gamma0CuspForms 162 :=
  etaQuotientCuspForm 162 sparse![162; 0 => -1, 1 => 2, 2 => 1, 5 => -1, 17 => 1, 26 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_162_eta_1m1_2p2_3p1_6m1_18p1_27p2_first_coeffs :
    first_coeffs 100 cuspForm_162_eta_1m1_2p2_3p1_6m1_18p1_27p2 =
    [0, 0, 0, 1, 1, 0, 0, -1, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, -1,
     0, -1, -1, 0, 0, 1, 0, 0, 1, 0, 0, -2, 0, 0, 2, 0, 0, 1, 0, 5,
     -1, 0, 0, 1, 0, 0, 1, 0, 4, 2, 0, 0, -1, 0, 0, -1, 0, -7, -1, 0,
     0, 1, 0, 0, -3, 0, 0, 1, 0, 0, -3, 0, 0, 3, 0, -5, 1, 0, 0, -3,
     0, 0, -3, 0, 2, 3, 0, 0, -3, 0, 0, 1, 0, -4, 4, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
