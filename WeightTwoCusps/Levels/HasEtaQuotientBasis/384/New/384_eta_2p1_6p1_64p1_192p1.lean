module

public import WeightTwoCusps.Tactic.Basic
public import WeightTwoCusps.Tactic.EtaCoefficient

/-!
# A cuspidal eta basis vector at level 384

The eta expression is `η(2z) η(6z) η(64z) η(192z)`; see
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

/-- The cuspidal eta quotient `η(2z) η(6z) η(64z) η(192z)` at level 384. -/
abbrev cuspForm_384_eta_2p1_6p1_64p1_192p1 : gamma0CuspForms 384 :=
  etaQuotientCuspForm 384 sparse![384; 1 => 1, 5 => 1, 63 => 1, 191 => 1]

/-- The coefficients of degrees zero through 99, including the constant term. -/
@[eta_simps] theorem cuspForm_384_eta_2p1_6p1_64p1_192p1_first_coeffs :
    first_coeffs 100 cuspForm_384_eta_2p1_6p1_64p1_192p1 =
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, -1, 0, -1, 0, 1,
     0, 2, 0, -1, 0, 2, 0, 0, 0, 0, 0, -1, 0, -1, 0, -1, 0, -1, 0, 0,
     0, 1, 0, -1, 0, -1, 0, 2, 0, 0, 0, 1, 0, 2, 0, 1, 0, -1, 0, 0,
     0, -1, 0, 2, 0, -1, 0, 0, 0, -1, 0, -1, 0, 0, 0, -2, 0, 0, 0, 1,
     0, 0, 0, -3, 0, 0, 0, 3, 0, -2, 0, -1, 0, 1, 0, 1, 0, 2, 0, 1] := by
  eta_coeff

end WeightTwoCusps
