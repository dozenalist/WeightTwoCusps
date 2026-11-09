module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 294

The eta expression is `η(z)^(-1) η(2z) η(3z)^2 η(6z)^(-1) η(7z) η(14z)^(-1) η(21z)^(-2) η(42z)^4 η(147z)^2 η(294z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(z)^(-1) η(2z) η(3z)^2 η(6z)^(-1) η(7z) η(14z)^(-1) η(21z)^(-2) η(42z)^4 η(147z)^2 η(294z)^(-1)` at level 294. -/
abbrev cuspForm_294_eta_1m1_2p1_3p2_6m1_7p1_14m1_21m2_42p4_147p2_294m1 : gamma0CuspForms 294 :=
  etaQuotientCuspForm 294 sparse![294; 0 => -1, 1 => 1, 2 => 2, 5 => -1, 6 => 1, 13 => -1, 20 => -2, 41 => 4, 146 => 2, 293 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_294_eta_1m1_2p1_3p2_6m1_7p1_14m1_21m2_42p4_147p2_294m1_first_coeffs :
    first_coeffs 100 cuspForm_294_eta_1m1_2p1_3p2_6m1_7p1_14m1_21m2_42p4_147p2_294m1 =
    [0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, -1, -1, 0, 0, 0, 0, -1,
     1, 0, 0, 0, -1, 0, 1, 1, 1, 0, 0, 2, 0, 0, -2, -1, 0, 0, -1, 0,
     -1, 0, -1, 0, 0, -1, 0, -2, 0, 0, 0, 0, -1, 0, 0, -2, 1, 0, 0, -1,
     0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0,
     -1, 0, 0, 3, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 2, 0, 1, 0, 0, 0] := by
  eta_coeff

end WeightTwoCusps
