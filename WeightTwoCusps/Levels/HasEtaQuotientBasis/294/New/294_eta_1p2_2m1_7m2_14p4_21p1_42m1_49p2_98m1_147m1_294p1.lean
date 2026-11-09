module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 294

The eta expression is `η(z)^2 η(2z)^(-1) η(7z)^(-2) η(14z)^4 η(21z) η(42z)^(-1) η(49z)^2 η(98z)^(-1) η(147z)^(-1) η(294z)`; see
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

/-- The cuspidal eta quotient `η(z)^2 η(2z)^(-1) η(7z)^(-2) η(14z)^4 η(21z) η(42z)^(-1) η(49z)^2 η(98z)^(-1) η(147z)^(-1) η(294z)` at level 294. -/
abbrev cuspForm_294_eta_1p2_2m1_7m2_14p4_21p1_42m1_49p2_98m1_147m1_294p1 : gamma0CuspForms 294 :=
  etaQuotientCuspForm 294 sparse![294; 0 => 2, 1 => -1, 6 => -2, 13 => 4, 20 => 1, 41 => -1, 48 => 2, 97 => -1, 146 => -1, 293 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_294_eta_1p2_2m1_7m2_14p4_21p1_42m1_49p2_98m1_147m1_294p1_first_coeffs :
    first_coeffs 100 cuspForm_294_eta_1p2_2m1_7m2_14p4_21p1_42m1_49p2_98m1_147m1_294p1 =
    [0, 0, 0, 0, 0, 0, 0, 1, -2, 0, 0, 2, 0, 0, 2, -4, -2, 0, 4, 0,
     0, 1, -2, -2, 0, 2, 0, 0, 1, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0, -4,
     0, 0, -1, 4, 2, 0, -4, 0, 0, 1, 2, 2, 0, 0, 0, 0, -4, 6, -4, 0,
     -4, 0, 0, -8, 10, 6, 0, -6, 0, 0, -6, 10, 4, 0, -10, 0, 0, -6, 10, 0,
     0, -4, 0, 0, 1, 2, 0, 0, 8, 0, 0, 2, -2, -10, 0, 4, 0, 0, -4, -4] := by
  eta_coeff

end WeightTwoCusps
