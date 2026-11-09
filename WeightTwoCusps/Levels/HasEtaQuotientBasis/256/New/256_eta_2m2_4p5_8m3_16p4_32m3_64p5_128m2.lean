module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 256

The eta expression is `η(2z)^(-2) η(4z)^5 η(8z)^(-3) η(16z)^4 η(32z)^(-3) η(64z)^5 η(128z)^(-2)`; see
[the local level table](../../TABLE.md#level-256).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(2z)^(-2) η(4z)^5 η(8z)^(-3) η(16z)^4 η(32z)^(-3) η(64z)^5 η(128z)^(-2)` at level 256. -/
abbrev cuspForm_256_eta_2m2_4p5_8m3_16p4_32m3_64p5_128m2 : gamma0CuspForms 256 :=
  etaQuotientCuspForm 256 sparse![256; 1 => -2, 3 => 5, 7 => -3, 15 => 4, 31 => -3, 63 => 5, 127 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_256_eta_2m2_4p5_8m3_16p4_32m3_64p5_128m2_first_coeffs :
    first_coeffs 100 cuspForm_256_eta_2m2_4p5_8m3_16p4_32m3_64p5_128m2 =
    [0, 1, 0, 2, 0, 0, 0, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, -2,
     0, 0, 0, 0, 0, -5, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0,
     0, 6, 0, -2, 0, 0, 0, 0, 0, -7, 0, 0, 0, 0, 0, 0, 0, -10, 0, -2,
     0, 0, 0, 0, 0, 0, 0, -10, 0, 0, 0, 0, 0, 0, 0, -10, 0, 0, 0, 0,
     0, -5, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2] := by
  eta_coeff

end WeightTwoCusps
