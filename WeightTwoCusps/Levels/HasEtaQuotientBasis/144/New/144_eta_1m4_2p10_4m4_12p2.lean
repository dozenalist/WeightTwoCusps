module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 144

The eta expression is `η(z)^(-4) η(2z)^10 η(4z)^(-4) η(12z)^2`; see
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

/-- The cuspidal eta quotient `η(z)^(-4) η(2z)^10 η(4z)^(-4) η(12z)^2` at level 144. -/
abbrev cuspForm_144_eta_1m4_2p10_4m4_12p2 : gamma0CuspForms 144 :=
  etaQuotientCuspForm 144 sparse![144; 0 => -4, 1 => 10, 3 => -4, 11 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_144_eta_1m4_2p10_4m4_12p2_first_coeffs :
    first_coeffs 100 cuspForm_144_eta_1m4_2p10_4m4_12p2 =
    [0, 1, 4, 4, 0, 4, 8, 0, 0, 4, 4, 8, 0, -2, 0, -8, 0, -4, -8, 4,
     0, 0, -8, -16, 0, -1, -8, 4, 0, -12, -16, -8, 0, -16, -4, 0, 0, 6, -16, -8,
     0, 12, 0, -4, 0, -8, 16, 0, 0, -7, -4, 8, 0, 4, 8, 8, 0, 16, -12, 8,
     0, -2, 32, 0, 0, -8, 32, 4, 0, 32, 0, 16, 0, 10, 24, -4, 0, 0, -16, 8,
     0, 4, 12, -8, 0, -4, 16, 24, 0, 12, 16, 0, 0, -32, 0, 16, 0, 2, -28, -16] := by
  eta_coeff

end WeightTwoCusps
