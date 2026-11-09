module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 294

The eta expression is `η(3z) η(7z)^(-1) η(14z)^2 η(21z)^2 η(42z)^(-1) η(49z)^(-1) η(98z)^2 η(147z) η(294z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(3z) η(7z)^(-1) η(14z)^2 η(21z)^2 η(42z)^(-1) η(49z)^(-1) η(98z)^2 η(147z) η(294z)^(-1)` at level 294. -/
abbrev cuspForm_294_eta_3p1_7m1_14p2_21p2_42m1_49m1_98p2_147p1_294m1 : gamma0CuspForms 294 :=
  etaQuotientCuspForm 294 sparse![294; 2 => 1, 6 => -1, 13 => 2, 20 => 2, 41 => -1, 48 => -1, 97 => 2, 146 => 1, 293 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_294_eta_3p1_7m1_14p2_21p2_42m1_49m1_98p2_147p1_294m1_first_coeffs :
    first_coeffs 100 cuspForm_294_eta_3p1_7m1_14p2_21p2_42m1_49m1_98p2_147p1_294m1 =
    [0, 1, 0, 0, -1, 0, 0, -1, 1, 0, 0, -1, 0, 0, -1, 0, 1, 0, 0, 0,
     0, 0, 0, 1, 0, 1, 0, 0, 1, -1, 0, 0, 2, 0, 0, 2, 0, -2, 0, 0,
     0, 0, 0, -2, -3, 0, 0, 0, 0, 1, -1, 0, 0, -2, 0, 0, -1, 1, 0, 0,
     -1, 0, 0, -1, -3, 3, 0, 4, 0, 0, 2, 1, 1, 0, 3, 0, 0, 0, -1, 0,
     0, 2, 0, 0, 2, 0, 0, 0, -2, 0, 0, -2, -1, -3, 0, -2, 0, 0, 1, -2] := by
  eta_coeff

end WeightTwoCusps
