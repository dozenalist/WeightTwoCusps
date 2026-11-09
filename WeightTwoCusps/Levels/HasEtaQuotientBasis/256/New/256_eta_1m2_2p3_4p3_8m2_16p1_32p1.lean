module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 256

The eta expression is `η(z)^(-2) η(2z)^3 η(4z)^3 η(8z)^(-2) η(16z) η(32z)`; see
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

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^3 η(4z)^3 η(8z)^(-2) η(16z) η(32z)` at level 256. -/
abbrev cuspForm_256_eta_1m2_2p3_4p3_8m2_16p1_32p1 : gamma0CuspForms 256 :=
  etaQuotientCuspForm 256 sparse![256; 0 => -2, 1 => 3, 3 => 3, 7 => -2, 15 => 1, 31 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_256_eta_1m2_2p3_4p3_8m2_16p1_32p1_first_coeffs :
    first_coeffs 100 cuspForm_256_eta_1m2_2p3_4p3_8m2_16p1_32p1 =
    [0, 0, 1, 2, 2, 4, 2, 0, 4, 0, 2, 6, 0, 4, 4, 0, 0, 0, 1, 2,
     4, 0, -2, 0, 0, 0, 2, -4, 0, 4, -4, 0, 0, 0, -2, 0, -6, -12, 2, 0,
     -8, 0, -8, -10, 0, -12, -4, 0, 0, 0, -1, -12, -12, 4, -4, 0, 0, 0, -6, 6,
     0, -12, 0, 0, 0, 0, -4, -14, 4, 0, -8, 0, -12, 0, 10, -10, 0, 0, -4, 0,
     0, 0, -6, 18, 0, -8, 6, 0, 0, 0, 2, 0, 0, 0, 8, 0, 0, 0, 9, 6] := by
  eta_coeff

end WeightTwoCusps
