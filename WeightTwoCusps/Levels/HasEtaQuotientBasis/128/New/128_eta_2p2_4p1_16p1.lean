module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 128

The eta expression is `η(2z)^2 η(4z) η(16z)`; see
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

/-- The cuspidal eta quotient `η(2z)^2 η(4z) η(16z)` at level 128. -/
abbrev cuspForm_128_eta_2p2_4p1_16p1 : gamma0CuspForms 128 :=
  etaQuotientCuspForm 128 sparse![128; 1 => 2, 3 => 1, 15 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_128_eta_2p2_4p1_16p1_first_coeffs :
    first_coeffs 100 cuspForm_128_eta_2p2_4p1_16p1 =
    [0, 1, 0, -2, 0, -2, 0, 4, 0, 1, 0, 2, 0, -2, 0, -4, 0, -2, 0, -2,
     0, 8, 0, -4, 0, -1, 0, 4, 0, 6, 0, 0, 0, -4, 0, 8, 0, -10, 0, -4,
     0, -6, 0, -6, 0, -2, 0, 8, 0, 9, 0, 4, 0, 6, 0, 4, 0, 4, 0, -14,
     0, -2, 0, 4, 0, 4, 0, -10, 0, -8, 0, -12, 0, 14, 0, 2, 0, -8, 0, 8,
     0, -11, 0, 6, 0, 4, 0, 12, 0, -2, 0, 8, 0, 0, 0, -4, 0, -2, 0, 2] := by
  eta_coeff

end WeightTwoCusps
