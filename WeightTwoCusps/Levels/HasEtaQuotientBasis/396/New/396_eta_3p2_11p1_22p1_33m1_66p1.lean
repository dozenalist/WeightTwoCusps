module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 396

The eta expression is `η(3z)^2 η(11z) η(22z) η(33z)^(-1) η(66z)`; see
[the local level table](../../TABLE.md#level-396).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(3z)^2 η(11z) η(22z) η(33z)^(-1) η(66z)` at level 396. -/
abbrev cuspForm_396_eta_3p2_11p1_22p1_33m1_66p1 : gamma0CuspForms 396 :=
  etaQuotientCuspForm 396 sparse![396; 2 => 2, 10 => 1, 21 => 1, 32 => -1, 65 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_396_eta_3p2_11p1_22p1_33m1_66p1_first_coeffs :
    first_coeffs 100 cuspForm_396_eta_3p2_11p1_22p1_33m1_66p1 =
    [0, 0, 0, 1, 0, 0, -2, 0, 0, -1, 0, 0, 2, 0, -1, 1, 0, 2, 2, 0,
     1, -2, 0, -2, 0, -2, -1, -2, 4, -2, -2, 2, 2, 1, -4, 0, 2, -2, 2, -4,
     -4, 2, 0, 4, -1, 7, 0, -1, 0, 4, 2, 6, 4, -1, -4, -2, -5, 0, 0, 1,
     -6, 0, -4, -6, -4, 2, 2, -6, 0, 3, 4, 4, -8, -4, 4, 0, 0, -1, 12, 0,
     -1, 1, 4, 4, 12, 4, 0, -8, 0, -5, 2, 0, -1, -9, 4, -6, -8, 2, 4, 3] := by
  eta_coeff

end WeightTwoCusps
