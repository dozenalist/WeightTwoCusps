module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 144

The eta expression is `η(z)^(-2) η(2z)^5 η(4z)^(-4) η(8z)^5 η(12z)^2 η(16z)^(-2)`; see
[the local level table](../../TABLE.md#level-144).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-2) η(2z)^5 η(4z)^(-4) η(8z)^5 η(12z)^2 η(16z)^(-2)` at level 144. -/
abbrev cuspForm_144_eta_1m2_2p5_4m4_8p5_12p2_16m2 : gamma0CuspForms 144 :=
  etaQuotientCuspForm 144 sparse![144; 0 => -2, 1 => 5, 3 => -4, 7 => 5, 11 => 2, 15 => -2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_144_eta_1m2_2p5_4m4_8p5_12p2_16m2_first_coeffs :
    first_coeffs 100 cuspForm_144_eta_1m2_2p5_4m4_8p5_12p2_16m2 =
    [0, 1, 2, 0, 0, 4, 4, 0, 0, 4, 2, 0, 0, -2, 0, 0, 0, -4, -4, 0,
     0, 0, -4, 0, 0, -1, -4, 0, 0, -12, -8, 0, 0, -16, -2, 0, 0, 6, -8, 0,
     0, 12, 0, 0, 0, -8, 8, 0, 0, -7, -2, 0, 0, 4, 4, 0, 0, 16, -6, 0,
     0, -2, 16, 0, 0, -8, 16, 0, 0, 32, 0, 0, 0, 10, 12, 0, 0, 0, -8, 0,
     0, 4, 6, 0, 0, -4, 8, 0, 0, 12, 8, 0, 0, -32, 0, 0, 0, 2, -14, 0] := by
  eta_coeff

end WeightTwoCusps
