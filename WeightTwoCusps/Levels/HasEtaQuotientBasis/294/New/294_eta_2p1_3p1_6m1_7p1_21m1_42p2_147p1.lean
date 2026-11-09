module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 294

The eta expression is `η(2z) η(3z) η(6z)^(-1) η(7z) η(21z)^(-1) η(42z)^2 η(147z)`; see
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

/-- The cuspidal eta quotient `η(2z) η(3z) η(6z)^(-1) η(7z) η(21z)^(-1) η(42z)^2 η(147z)` at level 294. -/
abbrev cuspForm_294_eta_2p1_3p1_6m1_7p1_21m1_42p2_147p1 : gamma0CuspForms 294 :=
  etaQuotientCuspForm 294 sparse![294; 1 => 1, 2 => 1, 5 => -1, 6 => 1, 20 => -1, 41 => 2, 146 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_294_eta_2p1_3p1_6m1_7p1_21m1_42p2_147p1_first_coeffs :
    first_coeffs 100 cuspForm_294_eta_2p1_3p1_6m1_7p1_21m1_42p2_147p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, -1, -1, 1, 0, 0, 0, 0, 2,
     2, 0, 0, -2, -1, 1, 0, 1, -2, -1, -1, 1, 1, -1, -3, -1, 0, 0, 2, 2,
     2, 0, 1, 2, 2, 0, -1, -4, 0, -1, 1, 0, -1, 0, -1, 1, 1, 1, 0, -4,
     -2, 1, 0, 3, -2, 1, 0, -1, 2, 1, -1, -2, -1, 1, 1, 1, 0, 2, -1, 3,
     0, -3, 1, -2, -2, -2, 1, 2, 0, 0, 0, 1, 3, -2, 2, -2, 0, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
