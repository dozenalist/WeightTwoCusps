module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 192

The eta expression is `η(z)^(-3) η(2z)^9 η(3z) η(4z)^(-3) η(6z)^(-3) η(12z) η(24z) η(32z)^2 η(64z)^(-1) η(96z)^(-1) η(192z)`; see
[the local level table](../../TABLE.md#level-192).
This is a vector of the complete cuspidal eta basis.

This form is defined directly as a cuspidal eta quotient. No normalized
Hecke newform or canonical newspace identification is asserted.
-/

set_option maxRecDepth 4096

@[expose] public section

noncomputable section

namespace WeightTwoCusps

open UpperHalfPlane

/-- The cuspidal eta quotient `η(z)^(-3) η(2z)^9 η(3z) η(4z)^(-3) η(6z)^(-3) η(12z) η(24z) η(32z)^2 η(64z)^(-1) η(96z)^(-1) η(192z)` at level 192. -/
abbrev cuspForm_192_eta_1m3_2p9_3p1_4m3_6m3_12p1_24p1_32p2_64m1_96m1_192p1 : gamma0CuspForms 192 :=
  etaQuotientCuspForm 192 sparse![192; 0 => -3, 1 => 9, 2 => 1, 3 => -3, 5 => -3, 11 => 1, 23 => 1, 31 => 2, 63 => -1, 95 => -1, 191 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_192_eta_1m3_2p9_3p1_4m3_6m3_12p1_24p1_32p2_64m1_96m1_192p1_first_coeffs :
    first_coeffs 100 cuspForm_192_eta_1m3_2p9_3p1_4m3_6m3_12p1_24p1_32p2_64m1_96m1_192p1 =
    [0, 0, 0, 0, 0, 1, 3, 0, -6, -3, 0, 0, 6, 0, -6, 0, 0, 6, 6, 0,
     0, -3, 0, 0, 6, 0, -12, 0, 0, -1, 0, 0, 0, -3, 0, 0, 0, -2, 0, 0,
     12, 6, 0, 0, -24, 3, 12, 0, 0, -12, 0, 0, 0, 11, 3, 0, 0, 3, 24, 0,
     -12, 2, -6, 0, 0, -6, -6, 0, 0, 0, -12, 0, -6, 0, 12, 0, 24, -12, -6, 0,
     0, 6, -24, 0, 0, -10, 0, 0, -24, 0, -12, 0, 48, 3, 12, 0, 0, 24, 0, 0] := by
  eta_coeff

end WeightTwoCusps
