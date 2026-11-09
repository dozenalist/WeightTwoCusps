module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 256

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-4) η(8z)^4 η(16z)^2 η(32z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-4) η(8z)^4 η(16z)^2 η(32z)^(-1)` at level 256. -/
abbrev cuspForm_256_eta_1m2_2p5_4m4_8p4_16p2_32m1 : gamma0CuspForms 256 :=
  etaQuotientCuspForm 256 sparse![256; 0 => -2, 1 => 5, 3 => -4, 7 => 4, 15 => 2, 31 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_256_eta_1m2_2p5_4m4_8p4_16p2_32m1_first_coeffs :
    first_coeffs 100 cuspForm_256_eta_1m2_2p5_4m4_8p4_16p2_32m1 =
    [0, 1, 2, 0, 0, 4, 4, 0, 0, 5, 4, 0, 0, 4, 8, 0, 0, 6, 2, 0,
     0, 0, -4, 0, 0, -5, 4, 0, 0, 4, -8, 0, 0, -8, -4, 0, 0, -12, 4, 0,
     0, 6, -16, 0, 0, -12, -8, 0, 0, -7, -2, 0, 0, 4, -8, 0, 0, -24, -12, 0,
     0, -12, 0, 0, 0, 0, -8, 0, 0, 0, -16, 0, 0, 2, 20, 0, 0, 0, -8, 0,
     0, 1, -12, 0, 0, -8, 12, 0, 0, 18, 4, 0, 0, 0, 16, 0, 0, -10, 18, 0] := by
  eta_coeff

end WeightTwoCusps
