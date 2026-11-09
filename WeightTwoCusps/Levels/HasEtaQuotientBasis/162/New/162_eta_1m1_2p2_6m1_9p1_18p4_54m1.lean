module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 162

The eta expression is `η(z)^(-1) η(2z)^2 η(6z)^(-1) η(9z) η(18z)^4 η(54z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(6z)^(-1) η(9z) η(18z)^4 η(54z)^(-1)` at level 162. -/
abbrev cuspForm_162_eta_1m1_2p2_6m1_9p1_18p4_54m1 : gamma0CuspForms 162 :=
  etaQuotientCuspForm 162 sparse![162; 0 => -1, 1 => 2, 5 => -1, 8 => 1, 17 => 4, 53 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_162_eta_1m1_2p2_6m1_9p1_18p4_54m1_first_coeffs :
    first_coeffs 100 cuspForm_162_eta_1m1_2p2_6m1_9p1_18p4_54m1 =
    [0, 1, 1, 0, 1, 0, 0, 2, 1, 0, 0, 0, 0, 2, 2, 0, 1, 0, 0, -1,
     -3, 0, -3, 0, 0, -5, -1, 0, 2, 0, 0, -4, -5, 0, -3, 0, 0, -4, 2, 0,
     0, 0, 0, -1, -6, 0, -6, 0, 0, -3, -2, 0, 2, 0, 0, 0, 2, 0, 6, 0,
     0, 8, 8, 0, 1, 0, 0, 5, 9, 0, 0, 0, 0, 11, -7, 0, -1, 0, 0, -4,
     3, 0, 9, 0, 0, 0, 2, 0, -3, 0, 0, 4, 6, 0, -6, 0, 0, 5, -3, 0] := by
  eta_coeff

end WeightTwoCusps
