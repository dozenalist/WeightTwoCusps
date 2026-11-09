module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 396

The eta expression is `η(z) η(2z) η(33z)^(-1) η(66z)^3`; see
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

/-- The cuspidal eta quotient `η(z) η(2z) η(33z)^(-1) η(66z)^3` at level 396. -/
abbrev cuspForm_396_eta_1p1_2p1_33m1_66p3 : gamma0CuspForms 396 :=
  etaQuotientCuspForm 396 sparse![396; 0 => 1, 1 => 1, 32 => -1, 65 => 3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_396_eta_1p1_2p1_33m1_66p3_first_coeffs :
    first_coeffs 100 cuspForm_396_eta_1p1_2p1_33m1_66p3 =
    [0, 0, 0, 0, 0, 0, 0, 1, -1, -2, 1, 0, 2, 1, 0, 0, -2, 1, -2, -2,
     0, 2, -1, 0, 2, 0, 2, 0, 1, 0, 0, -2, 0, 0, 0, -1, -2, -2, 0, 2,
     1, -1, -4, 4, 0, 2, 3, 0, 0, 0, 1, 0, -3, -2, 2, -1, 0, 0, 2, 2,
     -2, -1, -1, -2, 0, 0, 0, 0, -1, -2, -2, 0, 4, 0, 1, 0, 2, 0, 0, 3,
     0, 2, 2, -1, 2, 2, -2, -4, 1, 2, -4, 0, -2, -2, -7, -1, -2, 4, -1, 0] := by
  eta_coeff

end WeightTwoCusps
