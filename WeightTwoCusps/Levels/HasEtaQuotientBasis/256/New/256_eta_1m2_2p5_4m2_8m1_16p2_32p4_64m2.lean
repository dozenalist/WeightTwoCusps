module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 256

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(8z)^(-1) η(16z)^2 η(32z)^4 η(64z)^(-2)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(8z)^(-1) η(16z)^2 η(32z)^4 η(64z)^(-2)` at level 256. -/
abbrev cuspForm_256_eta_1m2_2p5_4m2_8m1_16p2_32p4_64m2 : gamma0CuspForms 256 :=
  etaQuotientCuspForm 256 sparse![256; 0 => -2, 1 => 5, 3 => -2, 7 => -1, 15 => 2, 31 => 4, 63 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_256_eta_1m2_2p5_4m2_8m1_16p2_32p4_64m2_first_coeffs :
    first_coeffs 100 cuspForm_256_eta_1m2_2p5_4m2_8m1_16p2_32p4_64m2 =
    [0, 1, 2, 0, 0, 2, 0, 0, 0, 1, 4, 0, 0, 2, 0, 0, 0, 2, 2, 0,
     0, 0, 0, 0, 0, 3, 4, 0, 0, 2, 0, 0, 0, -4, -4, 0, 0, -6, 0, 0,
     0, -2, -16, 0, 0, -6, 0, 0, 0, -7, -2, 0, 0, 2, 0, 0, 0, -12, -12, 0,
     0, -6, 0, 0, 0, 8, -8, 0, 0, 0, 0, 0, 0, -2, 20, 0, 0, 0, 0, 0,
     0, 5, -12, 0, 0, -4, 0, 0, 0, 14, 4, 0, 0, 0, 0, 0, 0, -14, 18, 0] := by
  eta_coeff

end WeightTwoCusps
