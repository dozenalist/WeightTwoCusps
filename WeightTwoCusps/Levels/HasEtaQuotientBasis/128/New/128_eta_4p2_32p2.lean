module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 128

The eta expression is `η(4z)^2 η(32z)^2`; see
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

/-- The cuspidal eta quotient `η(4z)^2 η(32z)^2` at level 128. -/
abbrev cuspForm_128_eta_4p2_32p2 : gamma0CuspForms 128 :=
  etaQuotientCuspForm 128 sparse![128; 3 => 2, 31 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_128_eta_4p2_32p2_first_coeffs :
    first_coeffs 100 cuspForm_128_eta_4p2_32p2 =
    [0, 0, 0, 1, 0, 0, 0, -2, 0, 0, 0, -1, 0, 0, 0, 2, 0, 0, 0, 1,
     0, 0, 0, 2, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, -4, 0, 0, 0, 2,
     0, 0, 0, 3, 0, 0, 0, -4, 0, 0, 0, -2, 0, 0, 0, -2, 0, 0, 0, 7,
     0, 0, 0, -2, 0, 0, 0, 5, 0, 0, 0, 6, 0, 0, 0, -1, 0, 0, 0, -4,
     0, 0, 0, -3, 0, 0, 0, -6, 0, 0, 0, -4, 0, 0, 0, 2, 0, 0, 0, -1] := by
  eta_coeff

end WeightTwoCusps
