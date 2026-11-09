module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 234

The eta expression is `η(z)^3 η(2z)^(-1) η(13z) η(26z)^(-1) η(78z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^3 η(2z)^(-1) η(13z) η(26z)^(-1) η(78z)^2` at level 234. -/
abbrev cuspForm_234_eta_1p3_2m1_13p1_26m1_78p2 : gamma0CuspForms 234 :=
  etaQuotientCuspForm 234 sparse![234; 0 => 3, 1 => -1, 12 => 1, 25 => -1, 77 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_234_eta_1p3_2m1_13p1_26m1_78p2_first_coeffs :
    first_coeffs 100 cuspForm_234_eta_1p3_2m1_13p1_26m1_78p2 =
    [0, 0, 0, 0, 0, 0, 1, -3, 1, 2, 2, -1, -4, 1, -2, 0, 2, 4, -1, 1,
     1, -2, -2, -4, -1, 2, -1, 6, 1, -2, -2, -1, 3, 2, -1, 0, 2, -2, 0, 0,
     -4, -4, 4, -2, 2, -8, 4, 5, 0, 0, 5, 6, -1, 0, 1, -6, -2, -2, -1, -2,
     -4, 2, -2, 2, -2, 1, -4, 5, 4, 0, 8, -2, -3, 4, -4, 2, 1, 4, -1, 8,
     -2, -10, -8, -6, 6, 8, -8, -8, -4, 2, 6, -1, -2, 2, 2, 0, 9, -8, 1, 10] := by
  eta_coeff

end WeightTwoCusps
