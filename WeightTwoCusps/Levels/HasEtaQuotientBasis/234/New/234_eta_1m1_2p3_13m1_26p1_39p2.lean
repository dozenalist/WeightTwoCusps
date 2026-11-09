module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 234

The eta expression is `η(z)^(-1) η(2z)^3 η(13z)^(-1) η(26z) η(39z)^2`; see
[the local level table](../../TABLE.md#level-234).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^3 η(13z)^(-1) η(26z) η(39z)^2` at level 234. -/
abbrev cuspForm_234_eta_1m1_2p3_13m1_26p1_39p2 : gamma0CuspForms 234 :=
  etaQuotientCuspForm 234 sparse![234; 0 => -1, 1 => 3, 12 => -1, 25 => 1, 38 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_234_eta_1m1_2p3_13m1_26p1_39p2_first_coeffs :
    first_coeffs 100 cuspForm_234_eta_1m1_2p3_13m1_26p1_39p2 =
    [0, 0, 0, 0, 1, 1, -1, 0, -1, -2, 1, -1, -1, 0, 1, 1, -1, 2, 1, 1,
     1, -1, -2, 0, 1, 0, 0, 0, 1, -2, 2, 0, 2, 2, -4, -2, -1, 0, -1, 1,
     0, 1, -2, 0, -3, 3, 3, -3, 1, -2, 2, 0, 1, -2, 2, -2, -1, -2, 2, 5,
     -3, 0, -1, 1, -2, 1, 0, 2, -1, 2, 0, 1, 3, -1, -4, 0, 2, -2, 0, 0,
     3, -2, 3, -1, 5, 2, 0, -2, -3, 3, 0, 0, 0, 0, -2, 2, -1, -1, -2, -6] := by
  eta_coeff

end WeightTwoCusps
