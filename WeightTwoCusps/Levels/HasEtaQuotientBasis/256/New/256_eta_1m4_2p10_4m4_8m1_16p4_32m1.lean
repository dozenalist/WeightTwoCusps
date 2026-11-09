module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 256

The eta expression is `η(z)^(-4) η(2z)^10 η(4z)^(-4) η(8z)^(-1) η(16z)^4 η(32z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^10 η(4z)^(-4) η(8z)^(-1) η(16z)^4 η(32z)^(-1)` at level 256. -/
abbrev cuspForm_256_eta_1m4_2p10_4m4_8m1_16p4_32m1 : gamma0CuspForms 256 :=
  etaQuotientCuspForm 256 sparse![256; 0 => -4, 1 => 10, 3 => -4, 7 => -1, 15 => 4, 31 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_256_eta_1m4_2p10_4m4_8m1_16p4_32m1_first_coeffs :
    first_coeffs 100 cuspForm_256_eta_1m4_2p10_4m4_8m1_16p4_32m1 =
    [0, 1, 4, 4, 0, 4, 8, 0, 0, 5, 8, 12, 0, 4, 16, 0, 0, 6, 4, 4,
     0, 0, -8, 0, 0, -5, 8, -8, 0, 4, -16, 0, 0, -8, -8, 0, 0, -12, 8, 0,
     0, 6, -32, -20, 0, -12, -16, 0, 0, -7, -4, -24, 0, 4, -16, 0, 0, -24, -24, 12,
     0, -12, 0, 0, 0, 0, -16, -28, 0, 0, -32, 0, 0, 2, 40, -20, 0, 0, -16, 0,
     0, 1, -24, 36, 0, -8, 24, 0, 0, 18, 8, 0, 0, 0, 32, 0, 0, -10, 36, 12] := by
  eta_coeff

end WeightTwoCusps
