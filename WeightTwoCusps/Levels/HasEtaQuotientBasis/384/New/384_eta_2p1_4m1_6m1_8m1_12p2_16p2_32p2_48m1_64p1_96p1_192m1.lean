module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 384

The eta expression is `η(2z) η(4z)^(-1) η(6z)^(-1) η(8z)^(-1) η(12z)^2 η(16z)^2 η(32z)^2 η(48z)^(-1) η(64z) η(96z) η(192z)^(-1)`; see
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

/-- The cuspidal eta quotient `η(2z) η(4z)^(-1) η(6z)^(-1) η(8z)^(-1) η(12z)^2 η(16z)^2 η(32z)^2 η(48z)^(-1) η(64z) η(96z) η(192z)^(-1)` at level 384. -/
abbrev cuspForm_384_eta_2p1_4m1_6m1_8m1_12p2_16p2_32p2_48m1_64p1_96p1_192m1 : gamma0CuspForms 384 :=
  etaQuotientCuspForm 384 sparse![384; 1 => 1, 3 => -1, 5 => -1, 7 => -1, 11 => 2, 15 => 2, 31 => 2, 47 => -1, 63 => 1, 95 => 1, 191 => -1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_384_eta_2p1_4m1_6m1_8m1_12p2_16p2_32p2_48m1_64p1_96p1_192m1_first_coeffs :
    first_coeffs 100 cuspForm_384_eta_2p1_4m1_6m1_8m1_12p2_16p2_32p2_48m1_64p1_96p1_192m1 =
    [0, 1, 0, -1, 0, 0, 0, 0, 0, 1, 0, -2, 0, 0, 0, 0, 0, 1, 0, -1,
     0, 0, 0, 0, 0, 2, 0, -1, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0,
     0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -2, 0, -1,
     0, 0, 0, 0, 0, -2, 0, 1, 0, 0, 0, 0, 0, -4, 0, 4, 0, 0, 0, 0,
     0, -2, 0, 6, 0, 0, 0, 0, 0, -5, 0, 4, 0, 0, 0, 0, 0, 1, 0, 1] := by
  eta_coeff

end WeightTwoCusps
