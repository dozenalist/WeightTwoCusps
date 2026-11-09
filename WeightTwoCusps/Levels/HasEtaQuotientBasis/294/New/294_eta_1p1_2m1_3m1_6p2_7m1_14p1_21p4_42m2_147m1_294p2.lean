module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 294

The eta expression is `η(z) η(2z)^(-1) η(3z)^(-1) η(6z)^2 η(7z)^(-1) η(14z) η(21z)^4 η(42z)^(-2) η(147z)^(-1) η(294z)^2`; see
[the local level table](../../TABLE.md#level-294).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z) η(2z)^(-1) η(3z)^(-1) η(6z)^2 η(7z)^(-1) η(14z) η(21z)^4 η(42z)^(-2) η(147z)^(-1) η(294z)^2` at level 294. -/
abbrev cuspForm_294_eta_1p1_2m1_3m1_6p2_7m1_14p1_21p4_42m2_147m1_294p2 : gamma0CuspForms 294 :=
  etaQuotientCuspForm 294 sparse![294; 0 => 1, 1 => -1, 2 => -1, 5 => 2, 6 => -1, 13 => 1, 20 => 4, 41 => -2, 146 => -1, 293 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_294_eta_1p1_2m1_3m1_6p2_7m1_14p1_21p4_42m2_147m1_294p2_first_coeffs :
    first_coeffs 100 cuspForm_294_eta_1p1_2m1_3m1_6p2_7m1_14p1_21p4_42m2_147m1_294p2 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
     -1, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, -1, 0, 1, 0, 1, 0, 0, -1, 0,
     -3, 3, 1, 0, 0, 2, 0, -3, 0, 1, 0, 0, 1, 0, -2, -1, -2, 0, 0, 1,
     0, 2, -1, -2, 0, 0, 0, 0, 3, -1, -1, 0, 0, 2, 0, 0, 3, 0, 0, 0,
     2, 0, 1, -2, 0, 0, 0, -1, 0, -2, 2, -3, 0, 0, 1, 0, 0, -2, -1, 0] := by
  eta_coeff

end WeightTwoCusps
