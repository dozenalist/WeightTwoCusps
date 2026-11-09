module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 64

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(8z)^3`; see
[the local level table](../../TABLE.md#level-64).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-2) η(8z)^3` at level 64. -/
abbrev cuspForm_64_eta_1m2_2p5_4m2_8p3 : gamma0CuspForms 64 :=
  etaQuotientCuspForm 64 sparse![64; 0 => -2, 1 => 5, 3 => -2, 7 => 3]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_64_eta_1m2_2p5_4m2_8p3_first_coeffs :
    first_coeffs 100 cuspForm_64_eta_1m2_2p5_4m2_8p3 =
    [0, 1, 2, 0, 0, 2, 0, 0, 0, -3, -4, 0, 0, -6, 0, 0, 0, 2, -6, 0,
     0, 0, 0, 0, 0, -1, 12, 0, 0, 10, 0, 0, 0, 0, 4, 0, 0, 2, 0, 0,
     0, 10, 0, 0, 0, -6, 0, 0, 0, -7, -2, 0, 0, -14, 0, 0, 0, 0, -20, 0,
     0, 10, 0, 0, 0, -12, 0, 0, 0, 0, 0, 0, 0, -6, -4, 0, 0, 0, 0, 0,
     0, 9, 20, 0, 0, 4, 0, 0, 0, 10, 12, 0, 0, 0, 0, 0, 0, 18, -14, 0] := by
  eta_coeff

end WeightTwoCusps
