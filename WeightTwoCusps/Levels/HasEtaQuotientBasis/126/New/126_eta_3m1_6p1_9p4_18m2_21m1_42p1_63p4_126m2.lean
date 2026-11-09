module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 126

The eta expression is `η(3z)^(-1) η(6z) η(9z)^4 η(18z)^(-2) η(21z)^(-1) η(42z) η(63z)^4 η(126z)^(-2)`; see
[the local level table](../../TABLE.md#level-126).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^(-1) η(6z) η(9z)^4 η(18z)^(-2) η(21z)^(-1) η(42z) η(63z)^4 η(126z)^(-2)` at level 126. -/
abbrev cuspForm_126_eta_3m1_6p1_9p4_18m2_21m1_42p1_63p4_126m2 : gamma0CuspForms 126 :=
  etaQuotientCuspForm 126 sparse![126; 2 => -1, 5 => 1, 8 => 4, 17 => -2, 20 => -1, 41 => 1, 62 => 4, 125 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_126_eta_3m1_6p1_9p4_18m2_21m1_42p1_63p4_126m2_first_coeffs :
    first_coeffs 100 cuspForm_126_eta_3m1_6p1_9p4_18m2_21m1_42p1_63p4_126m2 =
    [0, 1, 0, 0, 1, 0, 0, 1, 0, 0, -2, 0, 0, -2, 0, 0, -1, 0, 0, 0,
     0, 0, 2, 0, 0, -1, 0, 0, 1, 0, 0, -4, 0, 0, -2, 0, 0, 2, 0, 0,
     2, 0, 0, 4, 0, 0, -2, 0, 0, 1, 0, 0, -2, 0, 0, -4, 0, 0, 4, 0,
     0, 2, 0, 0, 1, 0, 0, -4, 0, 0, -2, 0, 0, 6, 0, 0, 0, 0, 0, 8,
     0, 0, 2, 0, 0, -4, 0, 0, -2, 0, 0, -2, 0, 0, 12, 0, 0, -2, 0, 0] := by
  eta_coeff

end WeightTwoCusps
