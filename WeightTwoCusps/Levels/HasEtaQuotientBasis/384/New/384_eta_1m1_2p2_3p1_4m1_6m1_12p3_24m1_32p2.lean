module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 384

The eta expression is `η(z)^(-1) η(2z)^2 η(3z) η(4z)^(-1) η(6z)^(-1) η(12z)^3 η(24z)^(-1) η(32z)^2`; see
[the local level table](../../TABLE.md#level-384).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-1) η(2z)^2 η(3z) η(4z)^(-1) η(6z)^(-1) η(12z)^3 η(24z)^(-1) η(32z)^2` at level 384. -/
abbrev cuspForm_384_eta_1m1_2p2_3p1_4m1_6m1_12p3_24m1_32p2 : gamma0CuspForms 384 :=
  etaQuotientCuspForm 384 sparse![384; 0 => -1, 1 => 2, 2 => 1, 3 => -1, 5 => -1, 11 => 3, 23 => -1, 31 => 2]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_384_eta_1m1_2p2_3p1_4m1_6m1_12p3_24m1_32p2_first_coeffs :
    first_coeffs 100 cuspForm_384_eta_1m1_2p2_3p1_4m1_6m1_12p3_24m1_32p2 =
    [0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, -2, -2, 0, 0, 1,
     -2, 0, 0, -2, 1, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, -2, -3, 0, 0, 0,
     -2, 0, 0, -1, 0, 0, 0, 4, 2, 0, 0, 0, 6, 0, 0, 2, 0, 0, 0, 3,
     0, 0, 0, 4, 0, 0, 0, 1, 2, 0, 0, -2, 1, 0, 0, -3, 0, 0, 0, 2,
     4, 0, 0, -5, 0, 0, 0, 6, -4, 0, 0, -4, 0, 0, 0, 2, 0, 0, 0, -1] := by
  eta_coeff

end WeightTwoCusps
