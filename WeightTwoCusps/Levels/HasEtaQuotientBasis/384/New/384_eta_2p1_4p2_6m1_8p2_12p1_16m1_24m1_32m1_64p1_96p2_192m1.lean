module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 384

The eta expression is `η(2z) η(4z)^2 η(6z)^(-1) η(8z)^2 η(12z) η(16z)^(-1) η(24z)^(-1) η(32z)^(-1) η(64z) η(96z)^2 η(192z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(2z) η(4z)^2 η(6z)^(-1) η(8z)^2 η(12z) η(16z)^(-1) η(24z)^(-1) η(32z)^(-1) η(64z) η(96z)^2 η(192z)^(-1)` at level 384. -/
abbrev cuspForm_384_eta_2p1_4p2_6m1_8p2_12p1_16m1_24m1_32m1_64p1_96p2_192m1 : gamma0CuspForms 384 :=
  etaQuotientCuspForm 384 sparse![384; 1 => 1, 3 => 2, 5 => -1, 7 => 2, 11 => 1, 15 => -1, 23 => -1, 31 => -1, 63 => 1, 95 => 2, 191 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_384_eta_2p1_4p2_6m1_8p2_12p1_16m1_24m1_32m1_64p1_96p2_192m1_first_coeffs :
    first_coeffs 100 cuspForm_384_eta_2p1_4p2_6m1_8p2_12p1_16m1_24m1_32m1_64p1_96p2_192m1 =
    [0, 1, 0, -1, 0, -3, 0, 3, 0, -2, 0, 1, 0, 12, 0, -9, 0, -2, 0, 5,
     0, -15, 0, 0, 0, 5, 0, -4, 0, 3, 0, 21, 0, -1, 0, -8, 0, 6, 0, -12,
     0, 0, 0, 3, 0, 3, 0, -18, 0, 3, 0, 2, 0, -21, 0, 18, 0, -5, 0, 5,
     0, 18, 0, 15, 0, -2, 0, 7, 0, 0, 0, -24, 0, 2, 0, -5, 0, 0, 0, -15,
     0, 1, 0, -9, 0, 6, 0, 9, 0, -8, 0, -2, 0, -9, 0, 30, 0, 4, 0, 7] := by
  eta_coeff

end WeightTwoCusps
