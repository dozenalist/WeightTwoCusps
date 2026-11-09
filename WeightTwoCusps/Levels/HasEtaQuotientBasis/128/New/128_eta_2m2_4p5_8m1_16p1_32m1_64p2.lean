module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 128

The eta expression is `η(2z)^(-2) η(4z)^5 η(8z)^(-1) η(16z) η(32z)^(-1) η(64z)^2`; see
[the local level table](../../TABLE.md#level-128).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-2) η(4z)^5 η(8z)^(-1) η(16z) η(32z)^(-1) η(64z)^2` at level 128. -/
abbrev cuspForm_128_eta_2m2_4p5_8m1_16p1_32m1_64p2 : gamma0CuspForms 128 :=
  etaQuotientCuspForm 128 sparse![128; 1 => -2, 3 => 5, 7 => -1, 15 => 1, 31 => -1, 63 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_128_eta_2m2_4p5_8m1_16p1_32m1_64p2_first_coeffs :
    first_coeffs 100 cuspForm_128_eta_2m2_4p5_8m1_16p1_32m1_64p2 =
    [0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 1, 0, -2, 0, 0, 0, 0,
     0, -4, 0, -2, 0, 0, 0, 0, 0, -3, 0, 0, 0, 0, 0, 0, 0, 5, 0, -2,
     0, 0, 0, 0, 0, 1, 0, 4, 0, 0, 0, 0, 0, -3, 0, 2, 0, 0, 0, 0,
     0, 1, 0, 2, 0, 0, 0, 0, 0, 4, 0, -6, 0, 0, 0, 0, 0, 4, 0, 4,
     0, 0, 0, 0, 0, -2, 0, 6, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
