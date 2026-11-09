module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 352

The eta expression is `η(8z)^(-2) η(16z)^7 η(32z)^(-3) η(44z)^2 η(176z)^(-1) η(352z)`; see
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

/-- The cuspidal eta quotient `η(8z)^(-2) η(16z)^7 η(32z)^(-3) η(44z)^2 η(176z)^(-1) η(352z)` at level 352. -/
abbrev cuspForm_352_eta_8m2_16p7_32m3_44p2_176m1_352p1 : gamma0CuspForms 352 :=
  etaQuotientCuspForm 352 sparse![352; 7 => -2, 15 => 7, 31 => -3, 43 => 2, 175 => -1, 351 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_352_eta_8m2_16p7_32m3_44p2_176m1_352p1_first_coeffs :
    first_coeffs 100 cuspForm_352_eta_8m2_16p7_32m3_44p2_176m1_352p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2,
     0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 0,
     0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, -4,
     0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 8,
     0, 0, 0, 6, 0, 0, 0, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -5] := by
  eta_coeff

end WeightTwoCusps
