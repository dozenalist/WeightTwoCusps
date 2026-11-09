module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 352

The eta expression is `η(4z)^2 η(16z)^(-1) η(32z) η(88z)^(-2) η(176z)^7 η(352z)^(-3)`; see
[the local level table](../../TABLE.md#level-352).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(4z)^2 η(16z)^(-1) η(32z) η(88z)^(-2) η(176z)^7 η(352z)^(-3)` at level 352. -/
abbrev cuspForm_352_eta_4p2_16m1_32p1_88m2_176p7_352m3 : gamma0CuspForms 352 :=
  etaQuotientCuspForm 352 sparse![352; 3 => 2, 15 => -1, 31 => 1, 87 => -2, 175 => 7, 351 => -3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_352_eta_4p2_16m1_32p1_88m2_176p7_352m3_first_coeffs :
    first_coeffs 100 cuspForm_352_eta_4p2_16m1_32p1_88m2_176p7_352m3 =
    [0, 1, 0, 0, 0, -2, 0, 0, 0, -1, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0,
     0, 0, 0, 0, 0, -3, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0,
     0, -2, 0, 0, 0, 2, 0, 0, 0, 1, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0,
     0, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0,
     0, 1, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
