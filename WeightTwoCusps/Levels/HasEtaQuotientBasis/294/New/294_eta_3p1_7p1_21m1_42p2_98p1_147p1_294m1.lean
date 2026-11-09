module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 294

The eta expression is `η(3z) η(7z) η(21z)^(-1) η(42z)^2 η(98z) η(147z) η(294z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(3z) η(7z) η(21z)^(-1) η(42z)^2 η(98z) η(147z) η(294z)^(-1)` at level 294. -/
abbrev cuspForm_294_eta_3p1_7p1_21m1_42p2_98p1_147p1_294m1 : gamma0CuspForms 294 :=
  etaQuotientCuspForm 294 sparse![294; 2 => 1, 6 => 1, 20 => -1, 41 => 2, 97 => 1, 146 => 1, 293 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_294_eta_3p1_7p1_21m1_42p2_98p1_147p1_294m1_first_coeffs :
    first_coeffs 100 cuspForm_294_eta_3p1_7p1_21m1_42p2_98p1_147p1_294m1 =
    [0, 1, 0, 0, -1, 0, 0, -1, -1, 0, 0, 1, 0, 0, 1, -1, 1, 0, 1, 0,
     0, 1, 2, -1, 0, -1, 0, 0, -1, -2, -1, 0, 1, 0, 0, 1, -1, 0, 0, 0,
     0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 1, -1, 0,
     0, 0, 0, -1, 1, 2, 0, -1, 0, 0, -1, 1, 1, 0, 0, 0, 0, 0, 0, 2,
     0, 0, 0, 0, 1, 0, -2, 0, 2, 0, 0, 1, 0, -3, 0, -2, 0, 0, 0, -1] := by
  eta_coeff

end WeightTwoCusps
